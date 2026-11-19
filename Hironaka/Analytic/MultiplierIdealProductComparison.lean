import Hironaka.Analytic.PotentialTheory.MultiplierIdeals
import Hironaka.Analytic.QuasiEquisingularBasics
import Hironaka.Analytic.StrongOpennessSliceInduction
import Hironaka.Manifold.ChartDifferentiable
import Hironaka.Analytic.HolomorphicGermAlgebra
import Hironaka.Analytic.PotentialTheory.ManifoldPluripolarBasic

set_option autoImplicit false

/-!
# The product inclusion of `lem:ideal-comparison`

Source: Copy-4, `lem:ideal-comparison`
(`transcendental-nakamaye-copy4-20260911`, `main-Nulllocus.tex:1666`), the first
inclusion of `eq:ideal-comparison`.

Copy-4 compares three ideals on the submanifold `V` — `𝔅 = 𝓘(ℓ φ_K)`, `𝔅̄_m` and
`𝔅̄_M` — and proves `𝔅 𝔅̄_m^p ⊆ 𝓘(Mu) ⊆ 𝔅̄_M`, with `ℓ C = M` and `m p = ℓ(C-1)`.
Note that `𝔅` is `𝓘(ℓ φ_K)`, not `𝓘(ℓ h_C)`: the step `𝓘(λ φ_K) ⊆ 𝓘(λ h_C)` is a
separate input (`eq:def-K`, `K ≼_𝓘 h_C`), available as
`Hironaka.multiplierIntegrableAt_of_moreSingularAt`.  Everything below is stated
for `𝓘(ℓ h_C)`, which is therefore the *larger* ideal and the stronger statement;
a consumer starting from `𝔅 = 𝓘(ℓ φ_K)` still owes that one inclusion.
The second inclusion is the trace inclusion fixed in `sec:setup`.  The first one
is the pointwise estimate

  `|f g|² e^{-M u} ≤ (|f|² e^{-ℓ h_C}) (|g|² e^{-ℓ(C-1) φ_m})`  almost everywhere,

which holds because `h_C ≤ C u - (C-1) φ_m` quasi-everywhere and `ℓ C = M`; the
first factor is integrable because `f` is a section of `𝔅`, and the second is
bounded because `g` is a section of `𝔅̄_m^{\,p}`
(`lem:trace-approximants`(iii), where the bound is asserted outside a pluripolar
set, hence almost everywhere).

This module proves that estimate, sorry-free, at the level of the Euclidean
model: `multiplierIntegrableAt_mul_of_add_le`.  Everything is written with the
two levels additive, `M = ℓ + r` and `r = ℓ(C-1) = m p`, so that the hypothesis
actually consumed contains no `EReal` subtraction; the manuscript's subtractive
form is converted into it by `ereal_smul_add_le_of_le_sub`, proved here in full,
including the degenerate combinations of `⊥` and `⊤` (at a point where
`φ_m = ⊥` and `u ≠ ⊥` the subtractive form is *vacuous*, and the additive form
holds anyway because `⊥` absorbs).

On the way this module records that
`Hironaka.HolomorphicIdealSheaves.multiplierIdeal` is an *ideal sheaf* — closed
under holomorphic multiples, finite sums, and therefore under `IsInSpanAt` of its
own sections — which nothing in the project had, and which is exactly what a
section of the product ideal `𝔅 𝔅̄_m^{\,p}` needs.  The inclusion is then stated
as `GermIdeal.Le`; the second factor is an arbitrary `GermIdeal`, since all that
is used of `𝔅̄_m^{\,p}` is that each of its sections satisfies
`lem:trace-approximants`(iii).  In particular the statement does not presuppose
the Step-1 ideal bookkeeping (`𝔠_M`, `G_M`, `G_m`, `𝔣_B`, `F_B`) that is still
owed.

No compactness, no Kähler form, and no input from the modification side, and no
`sorry` anywhere.

The two inputs are packaged as `ChartChainAt` and `ChartBoundedAt`, which read
the manuscript's two hypotheses *almost everywhere in the preferred chart*.
Copy-4 states both **quasi-everywhere**, so the descent is a real step and is
proved here rather than asserted: `chartChainAt_of_quasiEverywhere` and
`chartBoundedAt_of_quasiEverywhere` obtain both predicates from
`Hironaka.ManifoldPluripolar.QuasiEverywhere`, which is the vocabulary
`lem:positive-rooftop` actually delivers (`Hironaka.RooftopEnvelope`'s
`rooftopCompetitors` is defined by a `QuasiEverywhere` inequality).  So neither
predicate is a new interface standing between the manuscript and the Lean.
-/

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace Hironaka.MultiplierIdealProductComparison

noncomputable section



/-! ## The exponential inequality -/

/-- `e^{-X} ≤ e^{-A} e^{-B}` as soon as `A + B ≤ X`, provided neither `A` nor `B`
is `⊤`.  Both exclusions are needed, and symmetrically so: for `A = ⊤`, `B = ⊥`
one has `A + B = ⊥`, so the left side is `⊤` while the right side is
`0 * ⊤ = 0`; for `A = ⊥`, `B = ⊤` the same two values occur with the factors
exchanged. -/
theorem ereal_exp_neg_le_mul {A B X : EReal} (hA : A ≠ ⊤) (hB : B ≠ ⊤)
    (h : A + B ≤ X) :
    EReal.exp (-X) ≤ EReal.exp (-A) * EReal.exp (-B) :=
  calc EReal.exp (-X) ≤ EReal.exp (-(A + B)) :=
        EReal.exp_monotone (EReal.neg_le_neg_iff.mpr h)
    _ = EReal.exp (-A + -B) := by
        rw [EReal.neg_add (Or.inr hB) (Or.inl hA), sub_eq_add_neg]
    _ = EReal.exp (-A) * EReal.exp (-B) := EReal.exp_add _ _

/-- A nonnegative real multiple of an `EReal` that is not `⊤` is not `⊤`.  This is
`EReal.mul_ne_top` with its four side conditions discharged; it is named only
because it is used twice below. -/
theorem ereal_coe_mul_ne_top {c : ℝ} (hc : 0 ≤ c) {a : EReal} (ha : a ≠ ⊤) :
    (c : EReal) * a ≠ ⊤ :=
  (EReal.mul_ne_top _ _).mpr
    ⟨Or.inl (EReal.coe_ne_bot c), Or.inl (EReal.coe_nonneg.mpr hc),
      Or.inl (EReal.coe_ne_top c), Or.inr ha⟩

/-- The multiplicative form of the estimate: the weight at level `ℓ + r` of `u`
is dominated by the product of the weights at levels `ℓ` and `r` of `h_C` and
`φ_m`.  This is `e^{-Mu} ≤ e^{-ℓ h_C} e^{-r φ_m}`. -/
theorem multiplierWeight_add_le {ell r : ℝ} (hell : 0 ≤ ell) (hr : 0 ≤ r)
    {a b c : EReal} (ha : a ≠ ⊤) (hb : b ≠ ⊤)
    (h : (ell : EReal) * a + (r : EReal) * b ≤ ((ell + r : ℝ) : EReal) * c) :
    multiplierWeight (ell + r) c
      ≤ multiplierWeight ell a * multiplierWeight r b := by
  simpa only [multiplierWeight] using
    ereal_exp_neg_le_mul (ereal_coe_mul_ne_top hell ha)
      (ereal_coe_mul_ne_top hr hb) h

/-! ## The manuscript's subtractive form -/

/-- The manuscript's chain `h_C ≤ C u - (C-1) φ_m`, rewritten additively as
`ℓ h_C + ℓ(C-1) φ_m ≤ (ℓ C) u`.  All degenerate combinations of `⊥` and `⊤` in
`u` and `φ_m` are covered: the subtractive form is vacuous where
`(C-1) φ_m = ⊥`, and there the additive form holds because `⊥` absorbs. -/
theorem ereal_smul_add_le_of_le_sub {a u v : EReal} {ell C : ℝ}
    (hell : 0 ≤ ell)
    (h : a ≤ (C : EReal) * u - ((C - 1 : ℝ) : EReal) * v) :
    (ell : EReal) * a + ((ell * (C - 1) : ℝ) : EReal) * v
      ≤ ((ell * C : ℝ) : EReal) * u := by
  have hstep : a + ((C - 1 : ℝ) : EReal) * v ≤ (C : EReal) * u :=
    EReal.add_le_of_le_sub h
  have hdistrib : (ell : EReal) * a + ((ell * (C - 1) : ℝ) : EReal) * v
      = (ell : EReal) * (a + ((C - 1 : ℝ) : EReal) * v) := by
    rw [EReal.left_distrib_of_nonneg_of_ne_top (EReal.coe_nonneg.mpr hell)
      (EReal.coe_ne_top _), EReal.coe_mul, mul_assoc]
  rw [hdistrib, EReal.coe_mul, mul_assoc]
  exact mul_le_mul_of_nonneg_left hstep (EReal.coe_nonneg.mpr hell)

/-! ## The estimate of `lem:ideal-comparison`

The manuscript's `|fg|² e^{-Mu} ≤ (|f|² e^{-ℓ h_C})(|g|² e^{-r φ_m})`, and the
integrability it yields.
-/

/-- The pointwise estimate of `lem:ideal-comparison`: where the additive chain
`ℓ h_C + r φ_m ≤ M u` holds and neither `h_C` nor `φ_m` is `⊤`, the density of
`fg` at level `M = ℓ + r` against `u` is at most the product of the density of
`f` at level `ℓ` against `h_C` and the density of `g` at level `r` against
`φ_m`. -/
theorem multiplierDensity_mul_le {X : Type*} {u hC phim : X → EReal} {ell r : ℝ}
    (hell : 0 ≤ ell) (hr : 0 ≤ r) {f g : X → ℂ} {y : X}
    (hhC : hC y ≠ ⊤) (hphim : phim y ≠ ⊤)
    (hchain : (ell : EReal) * hC y + (r : EReal) * phim y
      ≤ ((ell + r : ℝ) : EReal) * u y) :
    multiplierDensity u (ell + r) (fun z => f z * g z) y
      ≤ multiplierDensity hC ell f y * multiplierDensity phim r g y := by
  have hw : multiplierWeight (ell + r) (u y)
      ≤ multiplierWeight ell (hC y) * multiplierWeight r (phim y) :=
    multiplierWeight_add_le hell hr hhC hphim hchain
  unfold multiplierDensity
  rw [norm_mul, mul_pow, ENNReal.ofReal_mul (sq_nonneg _)]
  calc ENNReal.ofReal (‖f y‖ ^ 2) * ENNReal.ofReal (‖g y‖ ^ 2) *
        multiplierWeight (ell + r) (u y)
      ≤ ENNReal.ofReal (‖f y‖ ^ 2) * ENNReal.ofReal (‖g y‖ ^ 2) *
        (multiplierWeight ell (hC y) * multiplierWeight r (phim y)) := by gcongr
    _ = ENNReal.ofReal (‖f y‖ ^ 2) * multiplierWeight ell (hC y) *
        (ENNReal.ofReal (‖g y‖ ^ 2) * multiplierWeight r (phim y)) := by ac_rfl

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E}

/-- **The first inclusion of `eq:ideal-comparison`, local form**
(Copy-4 `lem:ideal-comparison`).  If

* `f` is weighted-`L²` for `e^{-ℓ h_C}` near `x` (a section of `𝔅 = 𝓘(ℓ h_C)`),
* `g` is holomorphic on `U` with `|g|² e^{-r φ_m}` bounded almost everywhere on
  `U` (a section of `𝔅̄_m^{\,p}`, by `lem:trace-approximants`(iii)), and
* `ℓ h_C + r φ_m ≤ (ℓ + r) u` almost everywhere on `U`
  (`lem:positive-rooftop`, with `M = ℓ + r = ℓ C` and `r = ℓ(C-1) = m p`),

then `f g` is weighted-`L²` for `e^{-M u}` near `x`, i.e. `f g ∈ 𝓘(Mu)`.  The
quasi-plurisubharmonicity of `u` on `U` is used only for measurability of the
resulting density. -/
theorem multiplierIntegrableAt_mul_of_add_le
    {u hC phim : E → EReal} {ell r B : ℝ} {f g : E → ℂ} {x : E} {U : Set E}
    (hell : 0 < ell) (hr : 0 ≤ r) (hU : IsOpen U) (hxU : x ∈ U)
    (hu : QuasiPlurisubharmonicOn u U)
    (hhC : ∀ y ∈ U, hC y ≠ ⊤) (hphim : ∀ y ∈ U, phim y ≠ ⊤)
    (hchain : ∀ᵐ y ∂μ, y ∈ U →
      (ell : EReal) * hC y + (r : EReal) * phim y
        ≤ ((ell + r : ℝ) : EReal) * u y)
    (hg : DifferentiableOn ℂ g U)
    (hgb : ∀ᵐ y ∂μ, y ∈ U → multiplierDensity phim r g y ≤ ENNReal.ofReal B)
    (hf : MultiplierIntegrableAt hC ell f x μ) :
    MultiplierIntegrableAt u (ell + r) (fun y => f y * g y) x μ := by
  obtain ⟨-, U₀, hU₀, hxU₀, hfhol, hfint⟩ := hf
  set W := U ∩ U₀ with hWdef
  have hW : IsOpen W := hU.inter hU₀
  have hxW : x ∈ W := ⟨hxU, hxU₀⟩
  have hWU : W ⊆ U := inter_subset_left
  have hWU₀ : W ⊆ U₀ := inter_subset_right
  have hM : 0 < ell + r := by linarith
  have hhol : DifferentiableOn ℂ (fun y => f y * g y) W :=
    (hfhol.mono hWU₀).mul (hg.mono hWU)
  have hfW := hfint.mono hWU₀
  refine ⟨hM, W, hW, hxW, hhol, ?_, ?_⟩
  · exact aemeasurable_multiplierDensity_restrict_of_quasiPlurisubharmonicOn hW
      (hu.mono hWU) hM.ne' hhol.continuousOn
  · have hpoint : ∀ᵐ y ∂μ, y ∈ W →
        multiplierDensity u (ell + r) (fun z => f z * g z) y
          ≤ ENNReal.ofReal B * multiplierDensity hC ell f y := by
      filter_upwards [hchain, hgb] with y hy₁ hy₂ hyW
      calc multiplierDensity u (ell + r) (fun z => f z * g z) y
          ≤ multiplierDensity hC ell f y * multiplierDensity phim r g y :=
            multiplierDensity_mul_le hell.le hr (hhC y (hWU hyW))
              (hphim y (hWU hyW)) (hy₁ (hWU hyW))
        _ ≤ multiplierDensity hC ell f y * ENNReal.ofReal B := by
            gcongr
            exact hy₂ (hWU hyW)
        _ = ENNReal.ofReal B * multiplierDensity hC ell f y := mul_comm _ _
    calc (∫⁻ y in W, multiplierDensity u (ell + r) (fun z => f z * g z) y ∂μ)
        ≤ ∫⁻ y in W, ENNReal.ofReal B * multiplierDensity hC ell f y ∂μ :=
          setLIntegral_mono_ae' hW.measurableSet hpoint
      _ = ENNReal.ofReal B * ∫⁻ y in W, multiplierDensity hC ell f y ∂μ := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfW.2

/-! ## `𝓘(cφ)` is an ideal sheaf

Copy-4 uses the multiplier ideal as an ideal: `lem:ideal-comparison` compares the
*product* ideal `𝔅 𝔅̄_m^{\,p}` with `𝓘(Mu)`, and a section of a product ideal is a
finite sum `∑ aᵢ fᵢ gᵢ` with `aᵢ` holomorphic.  The three closure primitives are
`Hironaka.multiplierIntegrableAt_add`,
`Hironaka.multiplierIntegrableAt_differentiable_mul` and
`MultiplierIntegrableAt.congr`, and they were already assembled into an ideal of
germs *in one chart* by `Hironaka.StrongOpennessSliceInduction`
(`isHolomorphicGermIdeal_multiplierUnion`, against `Hironaka.GermIdealSliceClosure`).
What is new below is the same closure for the manifold-level
`Hironaka.HolomorphicIdealSheaves.multiplierIdeal`, whose membership is tested
in the *preferred* chart, so every step has to be transported through
`complexChartAt`.
-/

variable {n : ℕ} {Mfd : Type*} [TopologicalSpace Mfd]
  [ChartedSpace (ComplexModel n) Mfd] [IsComplexManifold n Mfd]

open HolomorphicIdealSheaves

omit [IsComplexManifold n Mfd] in
/-- The chart inverse of the preferred chart at `x` sends the neighbourhood filter
of the base point to the neighbourhood filter of `x`. -/
theorem tendsto_complexChartAt_symm (x : Mfd) :
    Filter.Tendsto (complexChartAt (n := n) x).val.symm
      (𝓝 ((complexChartAt (n := n) x).val x)) (𝓝 x) := by
  have hz : (complexChartAt (n := n) x).val x ∈ (complexChartAt (n := n) x).val.target :=
    (complexChartAt (n := n) x).val.map_source (mem_complexChartAt_source x)
  have hcont := ((complexChartAt (n := n) x).val.continuousAt_symm hz).tendsto
  rwa [(complexChartAt (n := n) x).val.left_inv (mem_complexChartAt_source x)] at hcont

omit [IsComplexManifold n Mfd] in
/-- Membership in `𝓘(cφ)` is a germ property of the holomorphic function. -/
theorem mem_multiplierIdeal_congr {φ : Mfd → EReal} {c : ℝ} {x : Mfd} {g h : Mfd → ℂ}
    (hg : (multiplierIdeal (n := n) c φ).mem x g) (hgh : g =ᶠ[𝓝 x] h) :
    (multiplierIdeal (n := n) c φ).mem x h :=
  ⟨HolomorphicAt.congr hg.1 hgh,
    hg.2.congr (Filter.Eventually.of_forall fun _ => rfl)
      ((tendsto_complexChartAt_symm x).eventually hgh)⟩

/-- `𝓘(cφ)` absorbs holomorphic multiples. -/
theorem mem_multiplierIdeal_holomorphic_mul {φ : Mfd → EReal} {c : ℝ} {x : Mfd}
    {a s : Mfd → ℂ} (ha : HolomorphicAt n a x)
    (hs : (multiplierIdeal (n := n) c φ).mem x s) :
    (multiplierIdeal (n := n) c φ).mem x (fun y => a y * s y) := by
  obtain ⟨U, hUsub, hU, hxU⟩ := _root_.mem_nhds_iff.mp ha
  set e := (complexChartAt (n := n) x).val with he
  have hz : e x ∈ e.target := e.map_source (mem_complexChartAt_source x)
  have hO : IsOpen (e.target ∩ e.symm ⁻¹' U) := e.isOpen_inter_preimage_symm hU
  have hzO : e x ∈ e.target ∩ e.symm ⁻¹' U := by
    refine ⟨hz, ?_⟩
    simpa [e.left_inv (mem_complexChartAt_source x)] using hxU
  have hdon : DifferentiableOn ℂ (fun z => a (e.symm z)) (e.target ∩ e.symm ⁻¹' U) :=
    differentiableOn_comp_chartSymm x (fun y hy => (hUsub hy).mdifferentiableWithinAt)
  have hdiff : ∀ᶠ z in 𝓝 (e x), DifferentiableAt ℂ (fun z' => a (e.symm z')) z := by
    filter_upwards [hO.mem_nhds hzO] with z hzmem
    exact hdon.differentiableAt (hO.mem_nhds hzmem)
  exact ⟨HolomorphicAt.mul ha hs.1, multiplierIntegrableAt_differentiable_mul hs.2 hdiff⟩

/-- `𝓘(cφ)` is closed under finite sums.  Quasi-plurisubharmonicity of `φ` enters
only through the measurability of the weight. -/
theorem mem_multiplierIdeal_sum {φ : Mfd → EReal}
    (hφ : ManifoldQuasiPlurisubharmonic (n := n) φ) {c : ℝ} (hc : 0 < c) {x : Mfd}
    {ι : Type*} (t : Finset ι) {F : ι → Mfd → ℂ}
    (hF : ∀ i ∈ t, (multiplierIdeal (n := n) c φ).mem x (F i)) :
    (multiplierIdeal (n := n) c φ).mem x (fun y => ∑ i ∈ t, F i y) := by
  classical
  have hz : (complexChartAt (n := n) x).val x
      ∈ (complexChartAt (n := n) x).val.target :=
    (complexChartAt (n := n) x).val.map_source (mem_complexChartAt_source x)
  have hqpsh : QuasiPlurisubharmonicAt
      (chartFunction φ (complexChartAt (n := n) x))
      ((complexChartAt (n := n) x).val x) := hφ _ _ hz
  induction t using Finset.induction with
  | empty =>
      refine ⟨?_, ?_⟩
      · simpa using holomorphicAt_const (n := n) (M := Mfd) (x := x) (0 : ℂ)
      · simpa using multiplierIntegrableAt_zero
          (chartFunction φ (complexChartAt (n := n) x)) hc _ volume
  | insert i t hit ih =>
      have hi := hF i (Finset.mem_insert_self i t)
      have hrest := ih (fun j hj => hF j (Finset.mem_insert_of_mem hj))
      refine mem_multiplierIdeal_congr (g := fun y => F i y + ∑ j ∈ t, F j y) ?_ ?_
      · exact ⟨HolomorphicAt.add hi.1 hrest.1,
          multiplierIntegrableAt_add hqpsh hi.2 hrest.2⟩
      · exact Filter.Eventually.of_forall fun y => by
          simp [Finset.sum_insert hit]

/-- `𝓘(cφ)` contains every germ that lies in the ideal its own sections generate:
`IsInSpanAt` presentations do not leave it. -/
theorem mem_multiplierIdeal_of_isInSpanAt {φ : Mfd → EReal}
    (hφ : ManifoldQuasiPlurisubharmonic (n := n) φ) {c : ℝ} (hc : 0 < c) {x : Mfd}
    {g : Mfd → ℂ}
    (h : IsInSpanAt (n := n) (fun s => (multiplierIdeal (n := n) c φ).mem x s) x g) :
    (multiplierIdeal (n := n) c φ).mem x g := by
  obtain ⟨-, N, s, a, hs, ha, heq⟩ := h
  refine mem_multiplierIdeal_congr (g := fun y => ∑ i, a i y * s i y) ?_ heq.symm
  exact mem_multiplierIdeal_sum hφ hc Finset.univ
    (fun i _ => mem_multiplierIdeal_holomorphic_mul (ha i) (hs i))

/-! ## `lem:ideal-comparison`, first inclusion, on a manifold -/

/-- The chain of `lem:positive-rooftop` read in the preferred chart at `x`:
`ℓ h_C + r φ_m ≤ (ℓ + r) u` almost everywhere on a neighbourhood of the base
point.  The manuscript's inequality holds quasi-everywhere, hence almost
everywhere, and it is the only place where `u` interacts with `h_C` and `φ_m`. -/
def ChartChainAt (u hC phim : Mfd → EReal) (ell r : ℝ) (x : Mfd) : Prop :=
  ∃ U : Set (ComplexModel n), IsOpen U ∧ (complexChartAt (n := n) x).val x ∈ U ∧
    ∀ᵐ z ∂(volume : Measure (ComplexModel n)), z ∈ U →
      (ell : EReal) * chartFunction hC (complexChartAt (n := n) x) z
          + (r : EReal) * chartFunction phim (complexChartAt (n := n) x) z
        ≤ ((ell + r : ℝ) : EReal) * chartFunction u (complexChartAt (n := n) x) z

/-- `lem:trace-approximants`(iii) read in the preferred chart at `x`: `b` is
holomorphic near `x` and `|b|² e^{-r φ_m}` is bounded almost everywhere on a
neighbourhood of the base point.  The manuscript asserts the bound outside a
pluripolar set, which is exactly this. -/
def ChartBoundedAt (phim : Mfd → EReal) (r : ℝ) (x : Mfd) (b : Mfd → ℂ) : Prop :=
  HolomorphicAt n b x ∧
    ∃ (U : Set (ComplexModel n)) (B : ℝ), IsOpen U ∧
      (complexChartAt (n := n) x).val x ∈ U ∧
      ∀ᵐ z ∂(volume : Measure (ComplexModel n)), z ∈ U →
        multiplierDensity (chartFunction phim (complexChartAt (n := n) x)) r
          (fun z' => b ((complexChartAt (n := n) x).val.symm z')) z
          ≤ ENNReal.ofReal B

/-- **`ChartChainAt` from the manuscript's quasi-everywhere chain.**
`lem:positive-rooftop` delivers `h_C ≤ C u - (C-1) φ_m` *quasi-everywhere*, i.e.
off a pluripolar set; a pluripolar set is Haar-null in every chart
(`ManifoldLocallyPluripolar.chart_measure_eq_zero`), which is exactly the
descent performed here.  The additive form of the chain is the one of
`ereal_smul_add_le_of_le_sub`. -/
theorem chartChainAt_of_quasiEverywhere {u hC phim : Mfd → EReal} {ell r : ℝ}
    (h : QuasiEverywhere (n := n) (fun y =>
      (ell : EReal) * hC y + (r : EReal) * phim y
        ≤ ((ell + r : ℝ) : EReal) * u y)) (x : Mfd) :
    ChartChainAt (n := n) u hC phim ell r x := by
  refine ⟨(complexChartAt (n := n) x).val.target,
    (complexChartAt (n := n) x).val.open_target,
    (complexChartAt (n := n) x).val.map_source (mem_complexChartAt_source x), ?_⟩
  have hae := h.ae_in_chart (complexChartAt (n := n) x) volume
  rw [ae_restrict_iff' (complexChartAt (n := n) x).val.open_target.measurableSet] at hae
  exact hae

/-- **`ChartBoundedAt` from a quasi-everywhere bound.**  `lem:trace-approximants`(iii)
asserts `|g|² e^{-r φ_m}` locally bounded *outside a pluripolar set*; this turns
that into the almost-everywhere bound in the preferred chart. -/
theorem chartBoundedAt_of_quasiEverywhere {phim : Mfd → EReal} {r B : ℝ} {x : Mfd}
    {b : Mfd → ℂ} (hb : HolomorphicAt n b x)
    (h : QuasiEverywhere (n := n) (fun y =>
      multiplierDensity phim r b y ≤ ENNReal.ofReal B)) :
    ChartBoundedAt (n := n) phim r x b := by
  refine ⟨hb, (complexChartAt (n := n) x).val.target, B,
    (complexChartAt (n := n) x).val.open_target,
    (complexChartAt (n := n) x).val.map_source (mem_complexChartAt_source x), ?_⟩
  have hae := h.ae_in_chart (complexChartAt (n := n) x) volume
  rw [ae_restrict_iff' (complexChartAt (n := n) x).val.open_target.measurableSet] at hae
  exact hae

/-- The generator step of `lem:ideal-comparison`: a section `f` of `𝓘(ℓ h_C)`
times a section `b` of `𝔅̄_m^{\,p}` lies in `𝓘(Mu)`, `M = ℓ + r`. -/
theorem mem_multiplierIdeal_mul_of_chartChain
    {u hC phim : Mfd → EReal} {ell r : ℝ} (hell : 0 < ell) (hr : 0 ≤ r) {x : Mfd}
    (hu : ManifoldQuasiPlurisubharmonic (n := n) u)
    (hhC : ManifoldQuasiPlurisubharmonic (n := n) hC)
    (hphim : ManifoldQuasiPlurisubharmonic (n := n) phim)
    (hchain : ChartChainAt (n := n) u hC phim ell r x)
    {f b : Mfd → ℂ}
    (hf : (multiplierIdeal (n := n) ell hC).mem x f)
    (hb : ChartBoundedAt (n := n) phim r x b) :
    (multiplierIdeal (n := n) (ell + r) u).mem x (fun y => f y * b y) := by
  obtain ⟨U₁, hU₁, hzU₁, hchain'⟩ := hchain
  obtain ⟨hbhol, U₂, B, hU₂, hzU₂, hbnd⟩ := hb
  obtain ⟨V, hVsub, hV, hxV⟩ := _root_.mem_nhds_iff.mp hbhol
  set e := (complexChartAt (n := n) x).val with he
  have hz : e x ∈ e.target := e.map_source (mem_complexChartAt_source x)
  have hVopen : IsOpen (e.target ∩ e.symm ⁻¹' V) := e.isOpen_inter_preimage_symm hV
  have hzV : e x ∈ e.target ∩ e.symm ⁻¹' V := by
    refine ⟨hz, ?_⟩
    simpa [e.left_inv (mem_complexChartAt_source x)] using hxV
  set W := (U₁ ∩ U₂) ∩ (e.target ∩ e.symm ⁻¹' V) with hWdef
  have hW : IsOpen W := (hU₁.inter hU₂).inter hVopen
  have hzW : e x ∈ W := ⟨⟨hzU₁, hzU₂⟩, hzV⟩
  have hWtarget : W ⊆ e.target := fun _ hy => hy.2.1
  refine ⟨HolomorphicAt.mul hf.1 hbhol, ?_⟩
  refine multiplierIntegrableAt_mul_of_add_le (U := W) (B := B) hell hr hW hzW
    ((hu (complexChartAt (n := n) x)).mono hWtarget)
    (fun y hy => (hhC (complexChartAt (n := n) x) y (hWtarget hy)).ne_top)
    (fun y hy => (hphim (complexChartAt (n := n) x) y (hWtarget hy)).ne_top)
    ?_ ?_ ?_ hf.2
  · filter_upwards [hchain'] with z hz' hzW'
    exact hz' hzW'.1.1
  · have hdon : DifferentiableOn ℂ (fun z => b (e.symm z)) (e.target ∩ e.symm ⁻¹' V) :=
      differentiableOn_comp_chartSymm x
        (fun y' hy' => (hVsub hy').mdifferentiableWithinAt)
    exact fun y hy => (hdon.differentiableAt (hVopen.mem_nhds hy.2)).differentiableWithinAt
  · filter_upwards [hbnd] with z hz' hzW'
    exact hz' hzW'.1.2

/-- **The first inclusion of `eq:ideal-comparison`** (Copy-4
`lem:ideal-comparison`): `𝔅 𝔅̄_m^{\,p} ⊆ 𝓘(Mu)` with `𝔅 = 𝓘(ℓ h_C)`,
`M = ℓ + r` and `r = ℓ(C-1) = m p`.  The second ideal is arbitrary: all that is
used of `𝔅̄_m^{\,p}` is that each of its sections satisfies
`lem:trace-approximants`(iii). -/
theorem multiplierIdeal_mul_le
    {u hC phim : Mfd → EReal} {ell r : ℝ} (hell : 0 < ell) (hr : 0 ≤ r)
    (hu : ManifoldQuasiPlurisubharmonic (n := n) u)
    (hhC : ManifoldQuasiPlurisubharmonic (n := n) hC)
    (hphim : ManifoldQuasiPlurisubharmonic (n := n) phim)
    (𝔟 : GermIdeal n Mfd)
    (hchain : ∀ x : Mfd, ChartChainAt (n := n) u hC phim ell r x)
    (hbnd : ∀ (x : Mfd) (b : Mfd → ℂ), 𝔟.mem x b → ChartBoundedAt (n := n) phim r x b) :
    ((multiplierIdeal (n := n) ell hC).mul 𝔟).Le
      (multiplierIdeal (n := n) (ell + r) u) := by
  intro x g hg
  obtain ⟨hgHol, N, s, a, hs, ha, heq⟩ := hg
  refine mem_multiplierIdeal_of_isInSpanAt hu (by linarith) ⟨hgHol, N, s, a, ?_, ha, heq⟩
  intro i
  obtain ⟨p, q, hp, hq, hpq⟩ := hs i
  rw [hpq]
  exact mem_multiplierIdeal_mul_of_chartChain hell hr hu hhC hphim (hchain x) hp
    (hbnd x q hq)

end

end Hironaka.MultiplierIdealProductComparison
