import Hironaka.Analytic.BergmanGenerators
import Hironaka.Analytic.OhsawaTakegoshiPoint
import Hironaka.Analytic.HolomorphicNormalFamilies
import Hironaka.Analytic.PotentialTheory.AnalyticSingularities
import Hironaka.Analytic.PshDiscLocalGlobal

set_option autoImplicit false

/-!
# The local Bergman kernel on the diagonal and its logarithm

This is the local model object of Demailly's regularization of a plurisubharmonic
function by Bergman kernels (Demailly, *Analytic methods in algebraic geometry*,
Theorem 13.2; Copy-4 `lem:regularization`, Step 1).

For a domain `D ⊆ ℂᵈ` and a weight `w : D → ℝ≥0∞` (in the application
`w = e^{-mP}`, i.e. `multiplierWeight m (P ·)`), the unit ball of the weighted
Bergman space is

  `bergmanBall D w = {f holomorphic on D | ∫_D |f|² w ≤ 1}`,

the Bergman kernel on the diagonal is the extremal value

  `bergmanSup D w y = sup {|f(y)|² | f ∈ bergmanBall D w}`,

and the Bergman weight is its logarithm `bergmanLog D w = log (bergmanSup D w)`.

The four facts that make `bergmanLog` a usable regularization are proved here.

* `bergmanSup_extremal`: the scaling/extremal property.  Any holomorphic `f` with
  `∫_D |f|² w ≤ A` satisfies `|f(y)|² ≤ A · bergmanSup D w y`; this is what turns an
  Ohsawa–Takegoshi extension into a lower bound for the kernel.
* `norm_le_bergmanBoundConst`: if `w ≥ δ > 0` on `D` and `closedBall y s ⊆ D`, then all
  of `bergmanBall D w` is bounded on `ball y (s/2)` by one explicit constant depending
  only on `δ`, `s` and `d`, by the sub-mean-value inequality for `|f|²`.
* `bergmanSup_lt_top` and `bergmanSup_le_add_mul_norm_sub`: local finiteness, and a local
  uniform Lipschitz estimate coming from the Cauchy estimates for the (now uniformly
  bounded) family; hence `bergmanLog` is upper semicontinuous
  (`upperSemicontinuousOn_bergmanLog`).
* `plurisubharmonicOn_bergmanLog`: `bergmanLog D w` is plurisubharmonic.  Each branch
  `y ↦ log |f(y)|²` is plurisubharmonic, the deficit `circleDeficit` is antitone in the
  potential, and the infimum over branches of the right-hand side of the submean
  inequality is the right-hand side for the supremum — the last step is
  `iInf_sub_toENNReal_le`, and it needs no regularization because the supremum is already
  upper semicontinuous.

Finally `exists_one_le_mul_bergmanSup` records the nondegeneracy coming from the L²
extension theorem from a point (`OhsawaTakegoshiPoint.exists_extension_from_point`):
for `w = e^{-cP}` one has `1 ≤ C e^{-cP(y)} · bergmanSup Ω w y` whenever `P(y) ≠ -∞`, so the
kernel is positive there and `bergmanLog Ω w y ≠ -∞`.  This is the lower bound that makes
`bergmanLog` a genuine approximation of `cP` rather than the constant `-∞`.
-/

open Set Filter MeasureTheory Metric
open scoped ENNReal Topology

namespace Hironaka.BergmanSupWeight

noncomputable section

open Hironaka

variable {d : ℕ} [MeasurableSpace (ComplexModel d)] [BorelSpace (ComplexModel d)]

/-- Unit ball of the weighted Bergman space on `D` for the weight `w`. -/
def bergmanBall (D : Set (ComplexModel d)) (w : ComplexModel d → ℝ≥0∞) :
    Set (ComplexModel d → ℂ) :=
  {f | DifferentiableOn ℂ f D ∧ ∫⁻ z in D, ENNReal.ofReal (‖f z‖ ^ 2) * w z ≤ 1}

/-- The Bergman kernel on the diagonal, as a supremum of point values. -/
def bergmanSup (D : Set (ComplexModel d)) (w : ComplexModel d → ℝ≥0∞)
    (y : ComplexModel d) : ℝ≥0∞ :=
  ⨆ f ∈ bergmanBall D w, ENNReal.ofReal (‖f y‖ ^ 2)

/-- Its logarithm, the Bergman weight. -/
def bergmanLog (D : Set (ComplexModel d)) (w : ComplexModel d → ℝ≥0∞)
    (y : ComplexModel d) : EReal :=
  ENNReal.log (bergmanSup D w y)

variable {D : Set (ComplexModel d)} {w : ComplexModel d → ℝ≥0∞}

theorem zero_mem_bergmanBall : (0 : ComplexModel d → ℂ) ∈ bergmanBall D w :=
  ⟨differentiableOn_const 0, by simp⟩

theorem bergmanBall_nonempty : (bergmanBall D w).Nonempty :=
  ⟨0, zero_mem_bergmanBall⟩

theorem le_bergmanSup {f : ComplexModel d → ℂ} (hf : f ∈ bergmanBall D w)
    (y : ComplexModel d) : ENNReal.ofReal (‖f y‖ ^ 2) ≤ bergmanSup D w y :=
  le_iSup₂ (f := fun f (_ : f ∈ bergmanBall D w) => ENNReal.ofReal (‖f y‖ ^ 2)) f hf

theorem bergmanSup_le {y : ComplexModel d} {a : ℝ≥0∞}
    (h : ∀ f ∈ bergmanBall D w, ENNReal.ofReal (‖f y‖ ^ 2) ≤ a) :
    bergmanSup D w y ≤ a :=
  iSup₂_le h

/-- `ENNReal.log` is an order isomorphism onto `EReal`, hence commutes with suprema. -/
theorem log_iSup {ι : Sort*} (F : ι → ℝ≥0∞) :
    ENNReal.log (⨆ i, F i) = ⨆ i, ENNReal.log (F i) :=
  ENNReal.logOrderIso.map_iSup F

/-- The Bergman weight is the supremum of the logarithms of the branches. -/
theorem bergmanLog_eq_iSup (y : ComplexModel d) :
    bergmanLog D w y = ⨆ f ∈ bergmanBall D w, logNormSq (f y) := by
  simp only [bergmanLog, bergmanSup, logNormSq, log_iSup]

theorem logNormSq_le_bergmanLog {f : ComplexModel d → ℂ} (hf : f ∈ bergmanBall D w)
    (y : ComplexModel d) : logNormSq (f y) ≤ bergmanLog D w y :=
  ENNReal.log_monotone (le_bergmanSup hf y)

/-- **Extremal property of the Bergman kernel.** A holomorphic function with weighted
`L²` norm at most `A` is dominated at every point by `A` times the kernel. -/
theorem bergmanSup_extremal {f : ComplexModel d → ℂ} (hf : DifferentiableOn ℂ f D)
    {A : ℝ≥0∞} (hA0 : A ≠ 0) (hAtop : A ≠ ⊤)
    (hint : ∫⁻ z in D, ENNReal.ofReal (‖f z‖ ^ 2) * w z ≤ A) (y : ComplexModel d) :
    ENNReal.ofReal (‖f y‖ ^ 2) ≤ A * bergmanSup D w y := by
  set a : ℝ := A.toReal with ha
  have ha0 : 0 < a := ENNReal.toReal_pos hA0 hAtop
  have haA : ENNReal.ofReal a = A := ENNReal.ofReal_toReal hAtop
  set g : ComplexModel d → ℂ := fun z => ((Real.sqrt a)⁻¹ : ℂ) * f z with hg
  have hnorm : ∀ z, ‖g z‖ ^ 2 = a⁻¹ * ‖f z‖ ^ 2 := by
    intro z
    simp only [hg, norm_mul, mul_pow, norm_inv, Complex.norm_real,
      Real.norm_of_nonneg (Real.sqrt_nonneg _), inv_pow, Real.sq_sqrt ha0.le]
  have hpt : ∀ z, ENNReal.ofReal (‖g z‖ ^ 2) * w z =
      ENNReal.ofReal a⁻¹ * (ENNReal.ofReal (‖f z‖ ^ 2) * w z) := by
    intro z
    rw [hnorm z, ENNReal.ofReal_mul (by positivity), mul_assoc]
  have hgmem : g ∈ bergmanBall D w := by
    refine ⟨hf.const_mul _, ?_⟩
    simp only [hpt]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    calc ENNReal.ofReal a⁻¹ * ∫⁻ z in D, ENNReal.ofReal (‖f z‖ ^ 2) * w z
        ≤ ENNReal.ofReal a⁻¹ * A := by gcongr
      _ = 1 := by
          rw [← haA, ← ENNReal.ofReal_mul (by positivity), inv_mul_cancel₀ ha0.ne',
            ENNReal.ofReal_one]
  have hinv : ENNReal.ofReal a⁻¹ = A⁻¹ := by
    rw [ENNReal.ofReal_inv_of_pos ha0, haA]
  have hle := le_bergmanSup hgmem y
  rw [hnorm y, ENNReal.ofReal_mul (by positivity), hinv] at hle
  calc ENNReal.ofReal (‖f y‖ ^ 2) = A * (A⁻¹ * ENNReal.ofReal (‖f y‖ ^ 2)) := by
        rw [← mul_assoc, ENNReal.mul_inv_cancel hA0 hAtop, one_mul]
    _ ≤ A * bergmanSup D w y := by gcongr

/-! ### Local uniform bounds -/

/-- The explicit uniform bound for the weighted Bergman unit ball on `ball y (s/2)` when the
weight is at least `δ` on `closedBall y s`: it depends only on `δ`, `s` and the dimension. -/
def bergmanBoundConst (d : ℕ) [MeasurableSpace (ComplexModel d)] [BorelSpace (ComplexModel d)]
    (δ s : ℝ) : ℝ :=
  Real.sqrt ((1 / (ENNReal.ofReal δ * volume (ball (0 : ComplexModel d) (s / 4)))).toReal)

theorem bergmanBoundConst_nonneg (d : ℕ) [MeasurableSpace (ComplexModel d)]
    [BorelSpace (ComplexModel d)] (δ s : ℝ) : 0 ≤ bergmanBoundConst d δ s :=
  Real.sqrt_nonneg _

/-- **Local uniform bound for the Bergman unit ball.**  If the weight is at least `δ > 0` on
`D` and `closedBall y s ⊆ D`, every element of `bergmanBall D w` is bounded on
`ball y (s/2)` by one constant depending only on `δ`, `s` and `d`.  This is the sub-mean-value
inequality for `|f|²` on the balls of radius `s/4` centred in `ball y (s/2)`. -/
theorem norm_le_bergmanBoundConst {δ s : ℝ} (hδ : 0 < δ) (hs : 0 < s) {y : ComplexModel d}
    (hsub : closedBall y s ⊆ D) (hlow : ∀ z ∈ D, ENNReal.ofReal δ ≤ w z)
    {f : ComplexModel d → ℂ} (hf : f ∈ bergmanBall D w)
    {z : ComplexModel d} (hz : z ∈ ball y (s / 2)) :
    ‖f z‖ ≤ bergmanBoundConst d δ s := by
  rw [bergmanBoundConst]
  set V : ℝ≥0∞ := volume (ball (0 : ComplexModel d) (s / 4)) with hV
  have hV0 : V ≠ 0 := (measure_ball_pos volume _ (by positivity)).ne'
  have hVtop : V ≠ ⊤ := measure_ball_lt_top.ne
  set B : ℝ≥0∞ := 1 / (ENNReal.ofReal δ * V) with hB
  have hBtop : B ≠ ⊤ := ENNReal.div_ne_top ENNReal.one_ne_top
    (mul_ne_zero (ENNReal.ofReal_pos.mpr hδ).ne' hV0)
  have hball : ball z (s / 2) ⊆ D := by
    intro u hu
    refine hsub ?_
    rw [mem_ball] at hz hu
    rw [mem_closedBall]
    have := dist_triangle u z y
    linarith
  have hsmall : ball z (s / 4) ⊆ ball z (s / 2) := ball_subset_ball (by linarith)
  have hmv := lintegral_ball_normSq_ge isOpen_ball (hf.1.mono hball)
    (by positivity : 0 < s / 4) (closedBall_subset_ball (by linarith))
  rw [Measure.addHaar_ball_center] at hmv
  have hchain : ENNReal.ofReal δ * (V * ENNReal.ofReal (‖f z‖ ^ 2)) ≤ 1 := by
    calc ENNReal.ofReal δ * (V * ENNReal.ofReal (‖f z‖ ^ 2))
        ≤ ENNReal.ofReal δ * ∫⁻ u in ball z (s / 4), ENNReal.ofReal (‖f u‖ ^ 2) := by gcongr
      _ = ∫⁻ u in ball z (s / 4), ENNReal.ofReal δ * ENNReal.ofReal (‖f u‖ ^ 2) :=
          (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm
      _ ≤ ∫⁻ u in ball z (s / 4), ENNReal.ofReal (‖f u‖ ^ 2) * w u := by
          refine setLIntegral_mono' measurableSet_ball fun u hu => ?_
          rw [mul_comm]
          gcongr
          exact hlow u (hball (hsmall hu))
      _ ≤ ∫⁻ u in D, ENNReal.ofReal (‖f u‖ ^ 2) * w u :=
          lintegral_mono_set (hsmall.trans hball)
      _ ≤ 1 := hf.2
  have hle : ENNReal.ofReal (‖f z‖ ^ 2) ≤ B := by
    rw [hB, ENNReal.le_div_iff_mul_le (Or.inl (mul_ne_zero
      (ENNReal.ofReal_pos.mpr hδ).ne' hV0)) (Or.inl (ENNReal.mul_ne_top
      ENNReal.ofReal_ne_top hVtop))]
    calc ENNReal.ofReal (‖f z‖ ^ 2) * (ENNReal.ofReal δ * V)
        = ENNReal.ofReal δ * (V * ENNReal.ofReal (‖f z‖ ^ 2)) := by ring
      _ ≤ 1 := hchain
  exact Real.le_sqrt_of_sq_le ((ENNReal.ofReal_le_iff_le_toReal hBtop).mp hle)

/-- **Local boundedness of the Bergman kernel** on the interior of `D`. -/
theorem bergmanSup_le_ofReal {δ s : ℝ} (hδ : 0 < δ) (hs : 0 < s) {y : ComplexModel d}
    (hsub : closedBall y s ⊆ D) (hlow : ∀ z ∈ D, ENNReal.ofReal δ ≤ w z)
    {z : ComplexModel d} (hz : z ∈ ball y (s / 2)) :
    bergmanSup D w z ≤ ENNReal.ofReal (bergmanBoundConst d δ s ^ 2) := by
  refine bergmanSup_le fun f hf => ENNReal.ofReal_le_ofReal ?_
  have h := norm_le_bergmanBoundConst hδ hs hsub hlow hf hz
  nlinarith [norm_nonneg (f z), bergmanBoundConst_nonneg d δ s]

theorem bergmanSup_lt_top {δ s : ℝ} (hδ : 0 < δ) (hs : 0 < s) {y : ComplexModel d}
    (hsub : closedBall y s ⊆ D) (hlow : ∀ z ∈ D, ENNReal.ofReal δ ≤ w z)
    {z : ComplexModel d} (hz : z ∈ ball y (s / 2)) :
    bergmanSup D w z < ⊤ :=
  lt_of_le_of_lt (bergmanSup_le_ofReal hδ hs hsub hlow hz) ENNReal.ofReal_lt_top

theorem bergmanSup_ne_top {δ s : ℝ} (hδ : 0 < δ) (hs : 0 < s) {y : ComplexModel d}
    (hsub : closedBall y s ⊆ D) (hlow : ∀ z ∈ D, ENNReal.ofReal δ ≤ w z)
    {z : ComplexModel d} (hz : z ∈ ball y (s / 2)) :
    bergmanSup D w z ≠ ⊤ :=
  (bergmanSup_lt_top hδ hs hsub hlow hz).ne

/-- Local finiteness of `bergmanSup` on an open `D` with a positive lower bound for the
weight. -/
theorem bergmanSup_ne_top_of_isOpen (hD : IsOpen D) {δ : ℝ} (hδ : 0 < δ)
    (hlow : ∀ z ∈ D, ENNReal.ofReal δ ≤ w z) {z : ComplexModel d} (hz : z ∈ D) :
    bergmanSup D w z ≠ ⊤ := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hD z hz
  refine bergmanSup_ne_top hδ (by positivity : 0 < ε / 2) ?_ hlow
    (mem_ball_self (by positivity))
  exact (closedBall_subset_ball (by linarith)).trans hball

theorem bergmanLog_ne_top_of_isOpen (hD : IsOpen D) {δ : ℝ} (hδ : 0 < δ)
    (hlow : ∀ z ∈ D, ENNReal.ofReal δ ≤ w z) {z : ComplexModel d} (hz : z ∈ D) :
    bergmanLog D w z ≠ ⊤ := by
  rw [bergmanLog, Ne, ENNReal.log_eq_top_iff]
  exact bergmanSup_ne_top_of_isOpen hD hδ hlow hz

/-! ### A local uniform Lipschitz estimate -/

/-- The Lipschitz constant, from the Cauchy estimate for a family bounded by
`bergmanBoundConst d δ s` on `ball y (s/2)`. -/
def bergmanLipConst (d : ℕ) [MeasurableSpace (ComplexModel d)] [BorelSpace (ComplexModel d)]
    (δ s : ℝ) : ℝ := 8 * bergmanBoundConst d δ s ^ 2 / s

theorem bergmanLipConst_nonneg (d : ℕ) [MeasurableSpace (ComplexModel d)]
    [BorelSpace (ComplexModel d)] {δ s : ℝ} (hs : 0 < s) :
    0 ≤ bergmanLipConst d δ s := by
  rw [bergmanLipConst]
  positivity

/-- **Local uniform Lipschitz estimate for the Bergman kernel.**  Since `bergmanBall D w` is
uniformly bounded on `ball y (s/2)`, the Cauchy estimates make the family
`z ↦ |f(z)|²` uniformly Lipschitz on `ball y (s/4)`, and hence so is its supremum. -/
theorem bergmanSup_le_add_mul_norm_sub {δ s : ℝ} (hδ : 0 < δ) (hs : 0 < s)
    {y : ComplexModel d} (hsub : closedBall y s ⊆ D)
    (hlow : ∀ z ∈ D, ENNReal.ofReal δ ≤ w z)
    {z₁ z₂ : ComplexModel d} (h₁ : z₁ ∈ ball y (s / 4)) (h₂ : z₂ ∈ ball y (s / 4)) :
    bergmanSup D w z₁ ≤
      bergmanSup D w z₂ + ENNReal.ofReal (bergmanLipConst d δ s * ‖z₁ - z₂‖) := by
  set L : ℝ := bergmanBoundConst d δ s with hL
  have hL0 : 0 ≤ L := bergmanBoundConst_nonneg d δ s
  have hhalf : ball y (s / 2) ⊆ D :=
    (ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith))).trans hsub
  have hq : s / 2 / 2 = s / 4 := by ring
  have h₁' : z₁ ∈ ball y (s / 2 / 2) := by rwa [hq]
  have h₂' : z₂ ∈ ball y (s / 2 / 2) := by rwa [hq]
  refine bergmanSup_le fun f hf => ?_
  have hbound : ∀ u ∈ ball y (s / 2), ‖f u‖ ≤ L :=
    fun u hu => norm_le_bergmanBoundConst hδ hs hsub hlow hf hu
  have hlip : ‖f z₁ - f z₂‖ ≤ L / (s / 4) * ‖z₁ - z₂‖ := by
    have h := Hironaka.norm_sub_le_of_forall_norm_le
      (by positivity : (0 : ℝ) < s / 2) (hf.1.mono hhalf) hbound h₁' h₂'
    rwa [hq] at h
  have hkey : ‖f z₁‖ ^ 2 ≤ ‖f z₂‖ ^ 2 + bergmanLipConst d δ s * ‖z₁ - z₂‖ := by
    have hb₁ : ‖f z₁‖ ≤ L := hbound z₁ (ball_subset_ball (by linarith) h₁)
    have hb₂ : ‖f z₂‖ ≤ L := hbound z₂ (ball_subset_ball (by linarith) h₂)
    have hdiff : ‖f z₁‖ - ‖f z₂‖ ≤ ‖f z₁ - f z₂‖ := norm_sub_norm_le _ _
    have hLc : bergmanLipConst d δ s * ‖z₁ - z₂‖ = 2 * L * (L / (s / 4) * ‖z₁ - z₂‖) := by
      rw [bergmanLipConst, ← hL]
      field_simp
      ring
    have hpq : (‖f z₁‖ - ‖f z₂‖) * (‖f z₁‖ + ‖f z₂‖) ≤
        ‖f z₁ - f z₂‖ * (‖f z₁‖ + ‖f z₂‖) :=
      mul_le_mul_of_nonneg_right hdiff (by positivity)
    have hp2 : ‖f z₁ - f z₂‖ * (‖f z₁‖ + ‖f z₂‖) ≤ ‖f z₁ - f z₂‖ * (2 * L) :=
      mul_le_mul_of_nonneg_left (by linarith) (norm_nonneg _)
    have hp3 : ‖f z₁ - f z₂‖ * (2 * L) ≤ (L / (s / 4) * ‖z₁ - z₂‖) * (2 * L) :=
      mul_le_mul_of_nonneg_right hlip (by positivity)
    rw [hLc]
    nlinarith [hpq, hp2, hp3]
  calc ENNReal.ofReal (‖f z₁‖ ^ 2)
      ≤ ENNReal.ofReal (‖f z₂‖ ^ 2 + bergmanLipConst d δ s * ‖z₁ - z₂‖) :=
        ENNReal.ofReal_le_ofReal hkey
    _ = ENNReal.ofReal (‖f z₂‖ ^ 2) + ENNReal.ofReal (bergmanLipConst d δ s * ‖z₁ - z₂‖) :=
        ENNReal.ofReal_add (by positivity)
          (mul_nonneg (bergmanLipConst_nonneg d hs) (norm_nonneg _))
    _ ≤ bergmanSup D w z₂ + ENNReal.ofReal (bergmanLipConst d δ s * ‖z₁ - z₂‖) := by
        gcongr
        exact le_bergmanSup hf z₂

/-- **Upper semicontinuity of the Bergman weight.**  The supremum `bergmanSup` is locally
Lipschitz and finite, so its logarithm is upper semicontinuous — in fact continuous. -/
theorem upperSemicontinuousOn_bergmanLog (hD : IsOpen D) {δ : ℝ} (hδ : 0 < δ)
    (hlow : ∀ z ∈ D, ENNReal.ofReal δ ≤ w z) :
    UpperSemicontinuousOn (bergmanLog D w) D := by
  intro x hx a hxa
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hD x hx
  set s : ℝ := ε / 2 with hs'
  have hs : 0 < s := by positivity
  have hsub : closedBall x s ⊆ D := (closedBall_subset_ball (by rw [hs']; linarith)).trans hball
  set K : ℝ := bergmanLipConst d δ s with hK
  have hK0 : 0 ≤ K := bergmanLipConst_nonneg d hs
  have hmono : ∀ z ∈ ball x (s / 4),
      bergmanLog D w z ≤ ENNReal.log (bergmanSup D w x + ENNReal.ofReal (K * ‖z - x‖)) :=
    fun z hz => ENNReal.log_monotone
      (bergmanSup_le_add_mul_norm_sub hδ hs hsub hlow hz (mem_ball_self (by positivity)))
  have hcont : ContinuousAt
      (fun z => ENNReal.log (bergmanSup D w x + ENNReal.ofReal (K * ‖z - x‖))) x := by
    have h1 : Continuous (fun z : ComplexModel d => ENNReal.ofReal (K * ‖z - x‖)) :=
      ENNReal.continuous_ofReal.comp
        (continuous_const.mul ((continuous_id.sub continuous_const).norm))
    exact (ENNReal.continuous_log.continuousAt).comp
      (continuousAt_const.add h1.continuousAt)
  have heven : ∀ᶠ z in 𝓝 x,
      ENNReal.log (bergmanSup D w x + ENNReal.ofReal (K * ‖z - x‖)) < a := by
    have htend : Tendsto
        (fun z => ENNReal.log (bergmanSup D w x + ENNReal.ofReal (K * ‖z - x‖))) (𝓝 x)
        (𝓝 (bergmanLog D w x)) := by
      have h := hcont.tendsto
      simpa [bergmanLog] using h
    exact htend (Iio_mem_nhds hxa)
  refine Filter.Eventually.filter_mono nhdsWithin_le_nhds ?_
  filter_upwards [heven, Metric.ball_mem_nhds x (by positivity : (0 : ℝ) < s / 4)] with z hz hzb
  exact lt_of_le_of_lt (hmono z hzb) hz

/-! ### Plurisubharmonicity -/

/-- **Exchange of a supremum with the deficit.**  The deficit `a ↦ (C - a)⁺` is antitone, and
the infimum of the deficits of a family is at most the deficit of its supremum.  This is the
only analytic ingredient needed to pass the disc submean inequality to a supremum of
potentials. -/
theorem iInf_sub_toENNReal_le {ι : Sort*} [Nonempty ι] (C : ℝ) (a : ι → EReal) :
    (⨅ i, ((C : EReal) - a i).toENNReal) ≤ ((C : EReal) - ⨆ i, a i).toENNReal := by
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  have hε' : (0 : ℝ) < (ε : ℝ) := by exact_mod_cast hε
  rw [← ENNReal.ofReal_coe_nnreal]
  have key : ∃ i, ((C : EReal) - a i).toENNReal ≤
      ((C : EReal) - ⨆ j, a j).toENNReal + ENNReal.ofReal (ε : ℝ) := by
    rcases eq_or_ne (⨆ j, a j) ⊥ with hbot | hbot
    · refine ⟨Classical.arbitrary ι, ?_⟩
      have hai : a (Classical.arbitrary ι) = ⊥ :=
        le_bot_iff.mp (hbot ▸ le_iSup a (Classical.arbitrary ι))
      rw [hai, hbot, EReal.coe_sub_bot]
      simp
    rcases eq_or_ne (⨆ j, a j) ⊤ with htop | htop
    · obtain ⟨i, hi⟩ := lt_iSup_iff.mp (htop ▸ EReal.coe_lt_top C)
      exact ⟨i, by rw [EReal.toENNReal_of_nonpos (EReal.sub_nonpos.mpr hi.le)]; exact zero_le⟩
    · set s : ℝ := (⨆ j, a j).toReal with hs
      have hseq : ((s : ℝ) : EReal) = ⨆ j, a j := EReal.coe_toReal htop hbot
      obtain ⟨i, hi⟩ : ∃ i, ((s - (ε : ℝ) : ℝ) : EReal) < a i := by
        refine lt_iSup_iff.mp ?_
        rw [← hseq]
        exact_mod_cast (by linarith : s - (ε : ℝ) < s)
      have hle : a i ≤ ((s : ℝ) : EReal) := hseq ▸ le_iSup a i
      have hne_bot : a i ≠ ⊥ := ne_bot_of_gt hi
      have hne_top : a i ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top s) hle
      set r : ℝ := (a i).toReal with hr
      have hreq : ((r : ℝ) : EReal) = a i := EReal.coe_toReal hne_top hne_bot
      have hrlt : s - (ε : ℝ) < r := by
        have := hi
        rw [← hreq] at this
        exact_mod_cast this
      refine ⟨i, ?_⟩
      rw [← hreq, ← hseq, ← EReal.coe_sub, ← EReal.coe_sub, EReal.real_coe_toENNReal,
        EReal.real_coe_toENNReal]
      calc ENNReal.ofReal (C - r) ≤ ENNReal.ofReal ((C - s) + (ε : ℝ)) :=
            ENNReal.ofReal_le_ofReal (by linarith)
        _ ≤ ENNReal.ofReal (C - s) + ENNReal.ofReal (ε : ℝ) := ENNReal.ofReal_add_le
  obtain ⟨i, hi⟩ := key
  exact (iInf_le _ i).trans hi

omit [MeasurableSpace (ComplexModel d)] [BorelSpace (ComplexModel d)] in
/-- Each branch `z ↦ log |f(z)|²` of the Bergman kernel is plurisubharmonic. -/
theorem plurisubharmonicOn_logNormSq_comp (hD : IsOpen D) {f : ComplexModel d → ℂ}
    (hf : DifferentiableOn ℂ f D) :
    PlurisubharmonicOn (fun z => logNormSq (f z)) D := by
  intro x hx
  have hgen : HolomorphicGeneratorsAt (fun _ : Fin 1 => f) x := ⟨D, hD, hx, fun _ => hf⟩
  have h := plurisubharmonicAt_scaled_generatorLog hgen (by norm_num : (0 : ℝ) < 1)
  have heq : (fun z => ((1 : ℝ) : EReal) * generatorLog (fun _ : Fin 1 => f) z)
      = fun z => logNormSq (f z) := by
    funext z
    rw [EReal.coe_one, one_mul, generatorLog]
    simp only [logNormSq]
    congr 2
    rw [generatorVector_norm_sq, generatorNormSq]
    simp
  rwa [heq] at h

theorem bergmanLog_eq_iSup_subtype (y : ComplexModel d) :
    bergmanLog D w y = ⨆ f : bergmanBall D w, logNormSq ((f : ComplexModel d → ℂ) y) := by
  rw [bergmanLog_eq_iSup]
  exact iSup_subtype' (p := fun f => f ∈ bergmanBall D w)
    (f := fun f _ => logNormSq (f y))

/-- **The Bergman weight satisfies the disc criterion.**  The deficit is antitone in the
potential, so the deficit of the supremum is at most the deficit of each branch; the branches
are plurisubharmonic, and `iInf_sub_toENNReal_le` turns the infimum of the branch bounds into
the bound for the supremum.  No regularization is needed: the supremum is already upper
semicontinuous by `upperSemicontinuousOn_bergmanLog`. -/
theorem discPshOn_bergmanLog (hD : IsOpen D) {δ : ℝ} (hδ : 0 < δ)
    (hlow : ∀ z ∈ D, ENNReal.ofReal δ ≤ w z) : DiscPshOn (bergmanLog D w) D := by
  have : Nonempty (bergmanBall D w) := ⟨⟨0, zero_mem_bergmanBall⟩⟩
  refine ⟨fun x hx => bergmanLog_ne_top_of_isOpen hD hδ hlow hx,
    upperSemicontinuousOn_bergmanLog hD hδ hlow, ?_⟩
  intro x v r hr hDisc C hC
  have hbranch : ∀ f : bergmanBall D w,
      circleDeficit (bergmanLog D w) x v r C ≤ ENNReal.ofReal (2 * Real.pi) *
        ((C : EReal) - logNormSq ((f : ComplexModel d → ℂ) x)).toENNReal := by
    rintro ⟨f, hf⟩
    have hpsh : DiscPshOn (fun z => logNormSq (f z)) D :=
      (plurisubharmonicOn_logNormSq_comp hD hf.1).discPshOn
    have hCf : ∀ y ∈ affineClosedDisc x v r, logNormSq (f y) ≤ (C : EReal) :=
      fun y hy => (logNormSq_le_bergmanLog hf y).trans (hC y hy)
    refine le_trans (circleDeficit_antitone (u := fun z => logNormSq (f z))
      (w := bergmanLog D w) x v r C fun t => logNormSq_le_bergmanLog hf _) ?_
    exact hpsh.submean x v r hr hDisc C hCf
  have hinf : circleDeficit (bergmanLog D w) x v r C ≤ ENNReal.ofReal (2 * Real.pi) *
      ⨅ f : bergmanBall D w, ((C : EReal) - logNormSq ((f : ComplexModel d → ℂ) x)).toENNReal := by
    rw [ENNReal.mul_iInf (fun h => absurd h ENNReal.ofReal_ne_top)]
    exact le_iInf hbranch
  refine hinf.trans ?_
  gcongr
  rw [bergmanLog_eq_iSup_subtype]
  exact iInf_sub_toENNReal_le (ι := ↥(bergmanBall D w)) C
    fun f => logNormSq ((f : ComplexModel d → ℂ) x)

/-- **The Bergman weight is plurisubharmonic** (Demailly, *Analytic methods in algebraic
geometry*, Theorem 13.2, Step 1). -/
theorem plurisubharmonicOn_bergmanLog (hD : IsOpen D) {δ : ℝ} (hδ : 0 < δ)
    (hlow : ∀ z ∈ D, ENNReal.ofReal δ ≤ w z) : PlurisubharmonicOn (bergmanLog D w) D :=
  (discPshOn_bergmanLog hD hδ hlow).plurisubharmonicOn hD

/-! ### Nondegeneracy from the L² extension theorem -/

omit [MeasurableSpace (ComplexModel d)] [BorelSpace (ComplexModel d)] in
theorem pos_of_one_le_mul {A S : ℝ≥0∞} (h : 1 ≤ A * S) : 0 < S := by
  rcases eq_or_ne S 0 with rfl | hS
  · simp at h
  · exact pos_iff_ne_zero.mpr hS

theorem bergmanLog_ne_bot_of_pos {y : ComplexModel d} (h : 0 < bergmanSup D w y) :
    bergmanLog D w y ≠ ⊥ := by
  rw [bergmanLog, Ne, ENNReal.log_eq_bot_iff]
  exact h.ne'

/-- **Nondegeneracy of the Bergman kernel.**  On a bounded open convex `Ω ⊆ ℂᵈ` with a
plurisubharmonic weight `P` and an exponent `c > 0`, the Ohsawa–Takegoshi extension from a
point produces a competitor `F` with `F y = 1` and `∫_Ω |F|² e^{-cP} ≤ C e^{-cP(y)}`, so the
extremal property `bergmanSup_extremal` gives `1 ≤ C e^{-cP(y)} · bergmanSup Ω w y`.  In
particular the kernel is positive and the Bergman weight is not `-∞` wherever `P` is finite:
this is the lower bound which makes `bergmanLog` a genuine approximation of `cP`. -/
theorem exists_one_le_mul_bergmanSup (d : ℕ) : by
    letI : MeasurableSpace (ComplexModel d) := borel _
    letI : BorelSpace (ComplexModel d) := ⟨rfl⟩
    exact ∀ R : ℝ, 0 < R → ∃ C : ℝ, 0 < C ∧
      ∀ Ω : Set (ComplexModel d), IsOpen Ω → Convex ℝ Ω → (∀ z ∈ Ω, ‖z‖ < R) →
      ∀ P : ComplexModel d → EReal, PlurisubharmonicOn P Ω → ∀ c : ℝ, 0 < c →
      ∀ y ∈ Ω, P y ≠ ⊥ →
        1 ≤ ENNReal.ofReal C * multiplierWeight c (P y) *
              bergmanSup Ω (fun z => multiplierWeight c (P z)) y ∧
          0 < bergmanSup Ω (fun z => multiplierWeight c (P z)) y ∧
          bergmanLog Ω (fun z => multiplierWeight c (P z)) y ≠ ⊥ := by
  let _ : MeasurableSpace (ComplexModel d) := borel _
  have _ : BorelSpace (ComplexModel d) := ⟨rfl⟩
  intro R hR
  obtain ⟨C, hC, hOT⟩ := OhsawaTakegoshiPoint.exists_extension_from_point d R hR
  refine ⟨C, hC, fun Ω hΩ hconv hbd P hP c hc y hy hPy => ?_⟩
  obtain ⟨F, hFhol, hFy, hFint⟩ := hOT Ω hΩ hconv hbd P hP c hc y hy
  have hPtop : P y ≠ ⊤ := (hP y hy).ne_top
  have hweq : multiplierWeight c (P y) = ENNReal.ofReal (Real.exp (-(c * (P y).toReal))) := by
    conv_lhs => rw [← EReal.coe_toReal hPtop hPy]
    rw [multiplierWeight_coe]
  have hwpos : multiplierWeight c (P y) ≠ 0 := by
    rw [hweq]; exact (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'
  have hwtop : multiplierWeight c (P y) ≠ ⊤ := by rw [hweq]; exact ENNReal.ofReal_ne_top
  have hA0 : ENNReal.ofReal C * multiplierWeight c (P y) ≠ 0 :=
    mul_ne_zero (ENNReal.ofReal_pos.mpr hC).ne' hwpos
  have hAtop : ENNReal.ofReal C * multiplierWeight c (P y) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hwtop
  have hint : ∫⁻ z in Ω, ENNReal.ofReal (‖F z‖ ^ 2) * multiplierWeight c (P z) ≤
      ENNReal.ofReal C * multiplierWeight c (P y) := hFint
  have hmain := bergmanSup_extremal hFhol hA0 hAtop hint y
  rw [hFy] at hmain
  simp only [norm_one, one_pow, ENNReal.ofReal_one] at hmain
  have hpos := pos_of_one_le_mul hmain
  exact ⟨hmain, hpos, bergmanLog_ne_bot_of_pos hpos⟩

end

end Hironaka.BergmanSupWeight
