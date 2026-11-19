import Hironaka.Analytic.QuantitativeRegularizationMultiplierGermFamily
import Hironaka.Analytic.QuantitativeRegularizationChartGermTransfer
import Hironaka.Analytic.QuantitativeRegularizationManifoldGermFamily
import Hironaka.Analytic.QuantitativeRegularizationBergmanInstanceTransport
import Hironaka.Analytic.LocalBergmanThetaBranch
import Hironaka.Analytic.IdealFunctionMaxGluing
import Hironaka.Analytic.PshConvexCone
import Hironaka.Analytic.FiniteBergmanOverlapLogSumCocycle

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The Bergman branch of one chart ball (Copy-4 `lem:regularization`, Steps 1 and 4)

Source: Copy-4, `lem:regularization`, Steps 1 and 4
(`references/transcendental-nakamaye-copy4-20260911/source/main-Nulllocus.tex:873-906,
1024-1060`); blueprint `ana:regularization`.

Copy-4 Step 1: on a coordinate ball `B_j` of the fixed cover, with `h_j` a smooth potential of
`-ζ`, `ψ_j = φ - h_j` is psh, `K_{j,m}` is the Bergman kernel of `e^{-mψ_j}` on `B_j`, and
`φ_{j,m} = m⁻¹ log K_{j,m} + h_j` satisfies `ζ + ddᶜφ_{j,m} ≥ 0` on `B_j`
(`eq:reg-local-positivity`).  Here `ρ = -h_j` is a smooth local potential of `ζ` in the chart
`e`, `Ψ = φ ∘ e⁻¹ + ρ` is the corrected weight, and the branch is

`chartBergmanBranch e B ρ φ m = m⁻¹ log K_{B, e^{-mΨ}} ∘ e - ρ ∘ e`   on `e⁻¹(B)`.

This module proves the three local properties `QuantitativeRegularizationMaxGluing` asks of a
branch:

* `thetaPlurisubharmonicOn_chartBergmanBranch` — `ζ`-PSH on the patch `e⁻¹(B)`
  (`eq:reg-local-positivity`): the Bergman log is psh (`BergmanSupWeight`), the weight
  being bounded below because `Ψ` is bounded above on the compact `B̄`; the transfer to an
  arbitrary chart is the one of `LocalBergmanThetaBranch`.
* `exists_ne_bot_chartBergmanBranch` — `-∞` on no open set: where `φ` is finite, the
  Ohsawa--Takegoshi extension from a point makes the kernel positive.
* `exists_const_eventually_le_chartBergmanBranch` — Step 4: near every point of the patch,
  `m⁻¹ log ∑ |gᵢ|² - C ≤` branch for every finite family of germs of `𝓘(mφ)`
  (`QuantitativeRegularizationMultiplierGermFamily` after `ChartGermTransfer`).

* `chartBergmanBranch_eq_of_potentials` — the branch does not depend on the choice of the
  potential `ρ` on a ball (Copy-4 Step 2's transformation rule: `σ - ρ = Re a`, `a`
  holomorphic, and multiplication by `e^{ma/2}` is an isometry of the weighted spaces).  This
  is what lets two branches be compared through one common potential.

All of these are statements about ONE chart ball, for a ball and a potential fixed in advance;
what remains of `lem:regularization` is the overlap of two branches in different charts with a
weight-independent constant, and the choice of the fixed cover.
-/

open Set Filter Metric MeasureTheory
open scoped Topology Manifold ContDiff ENNReal

namespace Hironaka.QuantitativeRegularizationChartBranch

open Hironaka.AnalyticGluingData Hironaka.HolomorphicIdealSheaves
  Hironaka.HolomorphicMaps Hironaka.LocalPotentialPullback BergmanSupWeight

noncomputable section

variable {d : ℕ} {Z : Type*} [TopologicalSpace Z]
  [ChartedSpace (ComplexModel d) Z] [IsComplexManifold d Z]

/-! ### The corrected weight and the branch -/

/-- The corrected chart weight `Ψ = φ ∘ e⁻¹ + ρ`. -/
def correctedWeight (e : ComplexChart d Z) (ρ : ComplexModel d → ℝ) (φ : Z → EReal) :
    ComplexModel d → EReal :=
  fun z => chartFunction φ e z + (ρ z : EReal)

/-- The patch `e⁻¹(B)` of a chart ball. -/
def chartPatch (e : ComplexChart d Z) (B : Set (ComplexModel d)) : Set Z :=
  e.val.source ∩ e.val ⁻¹' B

open Classical in
/-- **The Bergman branch of a chart ball**: `m⁻¹ log K_{B, e^{-mΨ}} ∘ e - ρ ∘ e` on the patch,
`0` elsewhere (the value off the patch is never read). -/
def chartBergmanBranch (e : ComplexChart d Z) (B : Set (ComplexModel d))
    (ρ : ComplexModel d → ℝ) (φ : Z → EReal) (m : ℕ) : Z → EReal :=
  fun x => if x ∈ chartPatch e B then
    (((m : ℝ)⁻¹ : ℝ) : EReal) *
        bergmanLog B (fun z => multiplierWeight m (correctedWeight e ρ φ z)) (e.val x) -
      (ρ (e.val x) : EReal)
    else 0

theorem isOpen_chartPatch (e : ComplexChart d Z) {B : Set (ComplexModel d)} (hB : IsOpen B) :
    IsOpen (chartPatch e B) :=
  e.val.isOpen_inter_preimage hB

theorem chartBergmanBranch_of_mem {e : ComplexChart d Z} {B : Set (ComplexModel d)}
    {ρ : ComplexModel d → ℝ} {φ : Z → EReal} {m : ℕ} {x : Z} (hx : x ∈ chartPatch e B) :
    chartBergmanBranch e B ρ φ m x =
      (((m : ℝ)⁻¹ : ℝ) : EReal) *
          bergmanLog B (fun z => multiplierWeight m (correctedWeight e ρ φ z)) (e.val x) -
        (ρ (e.val x) : EReal) := by
  simp only [chartBergmanBranch, if_pos hx]

/-! ### The corrected weight is psh and bounded above -/

/-- With `ρ` a smooth local potential of `ζ` on `Ω`, the corrected weight of a `ζ`-PSH `φ` is
psh on `Ω`. -/
theorem plurisubharmonicOn_correctedWeight {ζ : SmoothRealForm d Z 2} {φ : Z → EReal}
    (hφ : ThetaPlurisubharmonic ζ φ) {e : ComplexChart d Z} {Ω : Set (ComplexModel d)}
    {ρ : ComplexModel d → ℝ} (hρ : IsSmoothLocalPotential ζ e Ω ρ) :
    PlurisubharmonicOn (correctedWeight e ρ φ) Ω := by
  intro z hz
  have hφΩ : ThetaPlurisubharmonicOn ζ φ univ := fun e z hz _ => hφ e z hz
  exact IdealFunctionMaxGluing.ThetaPlurisubharmonicOn.plurisubharmonicAt_add_potential
    hφΩ e hρ hz trivial

/-- A psh function is bounded above by a real constant on a compact subset of its domain. -/
theorem exists_le_of_plurisubharmonicOn {u : ComplexModel d → EReal} {Ω K : Set (ComplexModel d)}
    (hu : PlurisubharmonicOn u Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    ∃ M : ℝ, ∀ z ∈ K, u z ≤ (M : EReal) := by
  rcases K.eq_empty_or_nonempty with rfl | hne
  · exact ⟨0, fun z hz => absurd hz (notMem_empty z)⟩
  have husc : UpperSemicontinuousOn u K := by
    intro x hx y hy
    obtain ⟨U, hU, hxU, hdisc⟩ := hu x (hKΩ hx)
    have h := hdisc.upperSemicontinuousOn x hxU y hy
    rw [nhdsWithin_eq_nhds.mpr (hU.mem_nhds hxU)] at h
    exact nhdsWithin_le_nhds h
  obtain ⟨a, haK, hmax⟩ := husc.exists_isMaxOn hne hK
  obtain ⟨U, -, haU, hdisc⟩ := hu a (hKΩ haK)
  have hatop : u a ≠ ⊤ := hdisc.ne_top a haU
  refine ⟨(u a).toReal, fun z hz => (hmax hz).trans (EReal.le_coe_toReal hatop)⟩

/-- **The weight `e^{-mΨ}` is bounded below by a positive constant** on a set where `Ψ` is
bounded above. -/
theorem ofReal_le_multiplierWeight {m : ℝ} (hm : 0 ≤ m) {a : EReal} {M : ℝ}
    (ha : a ≤ (M : EReal)) :
    ENNReal.ofReal (Real.exp (-(m * M))) ≤ multiplierWeight m a := by
  rw [← multiplierWeight_coe]
  exact multiplierWeight_antitone hm ha

/-! ### `eq:reg-local-positivity`: the branch is `ζ`-PSH on its patch -/

/-- The Bergman log of the corrected weight is psh on `B`, for `B` open with compact closure
inside the domain `Ω` of the potential. -/
theorem plurisubharmonicOn_bergmanLog_correctedWeight {ζ : SmoothRealForm d Z 2}
    {φ : Z → EReal} (hφ : ThetaPlurisubharmonic ζ φ) {e : ComplexChart d Z}
    {Ω B : Set (ComplexModel d)} {ρ : ComplexModel d → ℝ}
    (hρ : IsSmoothLocalPotential ζ e Ω ρ) (hBo : IsOpen B) (hBc : IsCompact (closure B))
    (hBΩ : closure B ⊆ Ω) (m : ℕ) :
    PlurisubharmonicOn
      (bergmanLog B (fun z => multiplierWeight m (correctedWeight e ρ φ z))) B := by
  obtain ⟨M, hM⟩ := exists_le_of_plurisubharmonicOn
    (plurisubharmonicOn_correctedWeight hφ hρ) hBc hBΩ
  refine plurisubharmonicOn_bergmanLog hBo (Real.exp_pos (-((m : ℝ) * M))) fun z hz => ?_
  exact ofReal_le_multiplierWeight (Nat.cast_nonneg m) (hM z (subset_closure hz))

/-- **`eq:reg-local-positivity`**: the chart Bergman branch is `ζ`-PSH on its patch. -/
theorem thetaPlurisubharmonicOn_chartBergmanBranch {ζ : SmoothRealForm d Z 2}
    {φ : Z → EReal} (hφ : ThetaPlurisubharmonic ζ φ) {e : ComplexChart d Z}
    {Ω B : Set (ComplexModel d)} {ρ : ComplexModel d → ℝ}
    (hρ : IsSmoothLocalPotential ζ e Ω ρ) (hBo : IsOpen B) (hBc : IsCompact (closure B))
    (hBΩ : closure B ⊆ Ω) {m : ℕ} (hm : 0 < m) :
    ThetaPlurisubharmonicOn ζ (chartBergmanBranch e B ρ φ m) (chartPatch e B) := by
  intro e' z hz hzpatch
  have hid : ContMDiff 𝓘(ℂ, ComplexModel d) 𝓘(ℂ, ComplexModel d) ∞ (id : Z → Z) :=
    contMDiff_id
  have hBΩ' : B ⊆ Ω := subset_closure.trans hBΩ
  have hρB : IsSmoothLocalPotential ζ e B ρ := hρ.mono hBo hBΩ'
  let F : ComplexModel d → ComplexModel d := coordinateMap (id : Z → Z) e' e
  let W : Set (ComplexModel d) := potentialDomain (id : Z → Z) e' e B
  let ρe : ComplexModel d → ℝ := ρ ∘ F
  have hW : IsOpen W := potentialDomain_isOpen hid e' e hBo
  have hzW : z ∈ W := by
    constructor
    · change z ∈ e'.val.target ∧ e'.val.symm z ∈ e.val.source
      exact ⟨hz, hzpatch.1⟩
    · change e.val (e'.val.symm z) ∈ B
      exact hzpatch.2
  have hρpull : IsSmoothLocalPotential (SmoothRealForm.pullback hid ζ) e' W ρe :=
    isSmoothLocalPotential_pullback hid e' hρB
  have hρe : IsSmoothLocalPotential ζ e' W ρe :=
    (SmoothRealForm.pullback_id_geometricallyEq ζ).localPotential_iff e' W ρe |>.mp hρpull
  refine ⟨W, ρe, hzW, hρe, ?_⟩
  have hcoef : 0 < ((m : ℝ)⁻¹) := inv_pos.mpr (by exact_mod_cast hm)
  have hdiff : DifferentiableOn ℂ F W :=
    ((coordinateMap_contDiffOn hid e' e).differentiableOn (by simp)).mono inter_subset_left
  have hlogpsh := plurisubharmonicOn_bergmanLog_correctedWeight hφ hρ hBo hBc hBΩ m
  intro y hy
  have hFy : F y ∈ B := hy.2
  have hscaled : PlurisubharmonicAt
      (fun w => (((m : ℝ)⁻¹ : ℝ) : EReal) *
        bergmanLog B (fun z => multiplierWeight m (correctedWeight e ρ φ z)) w) (F y) :=
    (hlogpsh (F y) hFy).const_mul hcoef
  have hpull := HolomorphicPullback.plurisubharmonicAt_comp_holomorphic hW hdiff hy hscaled
  refine hpull.congr ?_
  filter_upwards [hW.mem_nhds hy] with w hw
  have hwpatch : e'.val.symm w ∈ chartPatch e B := ⟨hw.1.2, hw.2⟩
  change (((m : ℝ)⁻¹ : ℝ) : EReal) *
      bergmanLog B (fun z => multiplierWeight m (correctedWeight e ρ φ z)) (F w) =
    chartBergmanBranch e B ρ φ m (e'.val.symm w) + (ρe w : EReal)
  rw [chartBergmanBranch_of_mem hwpatch]
  change (((m : ℝ)⁻¹ : ℝ) : EReal) *
      bergmanLog B (fun z => multiplierWeight m (correctedWeight e ρ φ z)) (F w) =
    ((((m : ℝ)⁻¹ : ℝ) : EReal) *
        bergmanLog B (fun z => multiplierWeight m (correctedWeight e ρ φ z)) (F w) -
      (ρ (F w) : EReal)) + (ρ (F w) : EReal)
  exact EReal.sub_add_cancel.symm


/-! ### The branch is `-∞` on no open set -/

/-- `c · a - r ≠ -∞` for `c > 0`, `a ≠ -∞` and `r` real. -/
theorem coe_mul_sub_coe_ne_bot {c : ℝ} (hc : 0 < c) {a : EReal} (ha : a ≠ ⊥) (r : ℝ) :
    (c : EReal) * a - (r : EReal) ≠ ⊥ := by
  induction a using EReal.rec with
  | bot => exact absurd rfl ha
  | top =>
      rw [EReal.coe_mul_top_of_pos hc]
      exact ne_of_gt (lt_of_lt_of_le (EReal.bot_lt_coe 0) (by simp))
  | coe t =>
      rw [← EReal.coe_mul, ← EReal.coe_sub]
      exact EReal.coe_ne_bot _

/-- **The branch is `-∞` on no open neighbourhood of a point of its patch**, for `B` open,
convex and bounded inside the domain of the potential: `φ` is finite somewhere in the
neighbourhood, and there the Ohsawa--Takegoshi extension from a point makes the Bergman kernel
positive (`BergmanSupWeight.exists_one_le_mul_bergmanSup`). -/
theorem exists_ne_bot_chartBergmanBranch {ζ : SmoothRealForm d Z 2} {φ : Z → EReal}
    (hφ : IsThetaPshPotential ζ φ) {e : ComplexChart d Z} {Ω B : Set (ComplexModel d)}
    {ρ : ComplexModel d → ℝ} (hρ : IsSmoothLocalPotential ζ e Ω ρ) (hBo : IsOpen B)
    (hBconv : Convex ℝ B) (hBbdd : Bornology.IsBounded B) (hBΩ : B ⊆ Ω) {m : ℕ} (hm : 0 < m)
    {x : Z} (hx : x ∈ chartPatch e B) {O : Set Z} (hO : IsOpen O) (hxO : x ∈ O) :
    ∃ y ∈ O, chartBergmanBranch e B ρ φ m y ≠ ⊥ := by
  obtain ⟨y, ⟨hyO, hypatch⟩, hyφ⟩ :=
    hφ.2 x (O ∩ chartPatch e B) (hO.inter (isOpen_chartPatch e hBo)) ⟨hxO, hx⟩
  refine ⟨y, hyO, ?_⟩
  rw [chartBergmanBranch_of_mem hypatch]
  -- the corrected weight is finite at `e y`
  have hΨy : correctedWeight e ρ φ (e.val y) ≠ ⊥ := by
    simp only [correctedWeight, chartFunction, e.val.left_inv hypatch.1]
    intro h
    rw [EReal.add_eq_bot_iff] at h
    rcases h with h | h
    · exact hyφ h
    · exact EReal.coe_ne_bot _ h
  have hΨpsh : PlurisubharmonicOn (correctedWeight e ρ φ) B :=
    plurisubharmonicOn_correctedWeight hφ.1 (hρ.mono hBo hBΩ)
  -- a radius bounding `B`
  obtain ⟨R₀, hR₀⟩ := hBbdd.subset_ball (0 : ComplexModel d)
  set R : ℝ := max R₀ 1 with hRdef
  have hR : 0 < R := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hnorm : ∀ z ∈ B, ‖z‖ < R := fun z hz => by
    have := hR₀ hz
    rw [mem_ball, dist_zero_right] at this
    exact lt_of_lt_of_le this (le_max_left _ _)
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  obtain ⟨C, -, hC⟩ := exists_one_le_mul_bergmanSup d R hR
  have hne := (hC B hBo hBconv hnorm (correctedWeight e ρ φ) hΨpsh (m : ℝ) hmR (e.val y)
    hypatch.2 hΨy).2.2
  rw [QuantitativeRegularizationBergmanInstanceTransport.bergmanLog_ambient_eq_borel]
  exact coe_mul_sub_coe_ne_bot (inv_pos.mpr hmR) hne _

/-! ### Step 4: the branch dominates every finite germ family of `𝓘(mφ)` -/

/-- EReal bookkeeping: `a - C ≤ L` and `r ≤ K` give `a - (C + K) ≤ L - r`. -/
theorem sub_add_le_sub_of_sub_le {a L : EReal} {C K r : ℝ} (h : a - (C : EReal) ≤ L)
    (hr : r ≤ K) : a - ((C + K : ℝ) : EReal) ≤ L - (r : EReal) := by
  have hsplit : a - ((C + K : ℝ) : EReal) = (a - (C : EReal)) - (K : EReal) := by
    rw [sub_eq_add_neg, sub_eq_add_neg, sub_eq_add_neg, ← EReal.coe_neg, ← EReal.coe_neg,
      ← EReal.coe_neg, neg_add, EReal.coe_add, add_assoc]
  rw [hsplit]
  exact EReal.sub_le_sub h (EReal.coe_le_coe_iff.mpr hr)

/-- **Copy-4 `lem:regularization`, Step 4, for one chart branch**: near every point of the
patch, `m⁻¹ log ∑ᵢ |gᵢ|² - C ≤` branch, for every finite family `g` of germs of `𝓘(mφ)` at the
point.  `B` is open with compact closure inside the convex `A ⋐ Ω`, `Ω` carrying the potential
`ρ`.  No generating system of `𝓘(mφ)` (hence no coherence) is used. -/
theorem exists_const_eventually_le_chartBergmanBranch (hd : 0 < d) {ζ : SmoothRealForm d Z 2}
    {φ : Z → EReal} (hφ : ThetaPlurisubharmonic ζ φ) {e : ComplexChart d Z}
    {A Ω : TopologicalSpace.Opens (ComplexModel d)} (hAconv : Convex ℝ (A : Set (ComplexModel d)))
    (hAΩ : MongeAmpere.RelativelyCompactIn A Ω) {ρ : ComplexModel d → ℝ}
    (hρ : IsSmoothLocalPotential ζ e Ω ρ) {B : Set (ComplexModel d)} (hBo : IsOpen B)
    (hBc : IsCompact (closure B)) (hBA : closure B ⊆ A) {m : ℕ} (hm : 0 < m) {x : Z}
    (hx : x ∈ chartPatch e B) {N : ℕ} {g : Fin N → Z → ℂ}
    (hg : ∀ i, (multiplierIdeal (n := d) (m : ℝ) φ).mem x (g i)) :
    ∃ C : ℝ, ∀ᶠ y in 𝓝 x,
      (((m : ℝ)⁻¹ : ℝ) : EReal) * generatorLog g y - (C : EReal) ≤
        chartBergmanBranch e B ρ φ m y := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hAΩ' : (A : Set (ComplexModel d)) ⊆ Ω := subset_closure.trans hAΩ.2
  have hexΩ : e.val x ∈ (Ω : Set (ComplexModel d)) :=
    hAΩ' (hBA (subset_closure hx.2))
  have hupsh : PlurisubharmonicOn (correctedWeight e ρ φ) Ω :=
    plurisubharmonicOn_correctedWeight hφ hρ
  have hρc : ContinuousOn ρ Ω := hρ.2.2.1.continuousOn
  -- the germ hypothesis, read in the chart `e` against the corrected weight
  have hint : ∀ i, MultiplierIntegrableAt (correctedWeight e ρ φ) (m : ℝ)
      (fun w => g i (e.val.symm w)) (e.val x) volume := fun i =>
    QuantitativeRegularizationChartGermTransfer.multiplierIntegrableAt_corrected_of_mem_multiplierIdeal
      hφ e Ω.isOpen hρc hupsh hmR hx.1 hexΩ (hg i)
  obtain ⟨S, hS⟩ := (hBc.isBounded.subset subset_closure).exists_norm_le
  obtain ⟨C, hC⟩ :=
    QuantitativeRegularizationMultiplierGermFamily.exists_const_eventually_generatorLog_le_bergmanLog_of_multiplierIntegrableAt
      hd hAconv hAΩ hupsh hmR hBo subset_closure hBc hBA hS hx.2 hint
  refine ⟨C + (ρ (e.val x) + 1), ?_⟩
  have hecont : ContinuousAt e.val x := e.val.continuousAt hx.1
  have hρcont : ContinuousAt (fun y => ρ (e.val y)) x :=
    (hρc.continuousAt (Ω.isOpen.mem_nhds hexΩ)).comp hecont
  filter_upwards [hecont.eventually hC,
    QuantitativeRegularizationManifoldGermFamily.generatorLog_comp_symm_eventuallyEq e hx.1 g,
    (isOpen_chartPatch e hBo).mem_nhds hx,
    hρcont.eventually (gt_mem_nhds (lt_add_one (ρ (e.val x))))] with y hy hgen hypatch hρy
  rw [chartBergmanBranch_of_mem hypatch]
  rw [hgen] at hy
  exact sub_add_le_sub_of_sub_le hy hρy.le


/-! ### The branch does not depend on the choice of potential -/

/-- `e^{-m(a + s)} = e^{-ms} e^{-ma}` for a real shift `s` and `m > 0`. -/
theorem multiplierWeight_add_coe {m : ℝ} (hm : 0 < m) (a : EReal) (s : ℝ) :
    multiplierWeight m (a + (s : EReal)) =
      ENNReal.ofReal (Real.exp (-(m * s))) * multiplierWeight m a := by
  induction a using EReal.rec with
  | bot =>
      rw [EReal.bot_add, multiplierWeight_bot hm, ENNReal.mul_top
        (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne']
  | top =>
      rw [EReal.top_add_coe, multiplierWeight_top hm, mul_zero]
  | coe t =>
      rw [← EReal.coe_add, multiplierWeight_coe, multiplierWeight_coe,
        ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
      congr 2
      ring

/-- `m⁻¹ (m c + L) - σ = m⁻¹ L - ρ` when `c = σ - ρ`, in `EReal`, for every `L`. -/
theorem inv_mul_coe_add_sub {m : ℝ} (hm : 0 < m) (L : EReal) (σ ρ : ℝ) :
    ((m⁻¹ : ℝ) : EReal) * (((m * (σ - ρ) : ℝ) : EReal) + L) - (σ : EReal) =
      ((m⁻¹ : ℝ) : EReal) * L - (ρ : EReal) := by
  induction L using EReal.rec with
  | bot =>
      rw [EReal.add_bot, EReal.coe_mul_bot_of_pos (inv_pos.mpr hm)]
      rfl
  | top =>
      rw [EReal.add_top_of_ne_bot (EReal.coe_ne_bot _),
        EReal.coe_mul_top_of_pos (inv_pos.mpr hm)]
      rfl
  | coe t =>
      rw [← EReal.coe_add, ← EReal.coe_mul, ← EReal.coe_sub, ← EReal.coe_mul, ← EReal.coe_sub]
      congr 1
      field_simp
      ring

/-- **The chart branch does not depend on the potential**: for two smooth local potentials
`ρ`, `σ` of `ζ` on a ball `ball x₀ r` of the chart and `B ⊆ ball x₀ (r/2)`, the two branches
agree on the patch.  `σ - ρ` is the real part of a holomorphic function on the half ball
(`FiniteBergmanOverlapLogSumCocycle.exists_holomorphic_additiveTransition_of_localPotentialsOnBall`),
and multiplication by its exponential is an isometry of the weighted Bergman spaces
(`BergmanHolomorphicMultiplier.bergmanSup_exp_weight`), shifting `m⁻¹ log K` by exactly
`σ - ρ`.  This is the "transformation rule for Bergman kernels" of Copy-4 Step 2. -/
theorem chartBergmanBranch_eq_of_potentials {ζ : SmoothRealForm d Z 2} {e : ComplexChart d Z}
    {x₀ : ComplexModel d} {r : ℝ} (hr : 0 < r) {ρ σ : ComplexModel d → ℝ}
    (hρ : IsSmoothLocalPotential ζ e (ball x₀ r) ρ)
    (hσ : IsSmoothLocalPotential ζ e (ball x₀ r) σ) {B : Set (ComplexModel d)}
    (hBo : IsOpen B) (hB : B ⊆ ball x₀ (r / 2)) (φ : Z → EReal) {m : ℕ} (hm : 0 < m)
    {x : Z} (hx : x ∈ chartPatch e B) :
    chartBergmanBranch e B σ φ m x = chartBergmanBranch e B ρ φ m x := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  obtain ⟨g, hg, hre⟩ :=
    FiniteBergmanOverlapLogSumCocycle.exists_holomorphic_additiveTransition_of_localPotentialsOnBall
      e hr hρ hσ
  set a : ComplexModel d → ℂ := fun z => ((m : ℂ) / 2) * g z with hadef
  have ha : DifferentiableOn ℂ a B := ((differentiableOn_const _).mul hg).mono hB
  have hare : ∀ z ∈ B, (a z).re = (m : ℝ) / 2 * (σ z - ρ z) := by
    intro z hz
    simp only [hadef, Complex.mul_re, Complex.div_ofNat_re, Complex.natCast_re,
      Complex.div_ofNat_im, Complex.natCast_im, zero_div, zero_mul, sub_zero, hre z (hB hz)]
  -- the two weights differ by the factor `e^{-2 Re a}` on `B`
  have hweight : ∀ z ∈ B, multiplierWeight m (correctedWeight e σ φ z) =
      ENNReal.ofReal (Real.exp (-(2 * (a z).re))) *
        multiplierWeight m (correctedWeight e ρ φ z) := by
    intro z hz
    have hsplit : correctedWeight e σ φ z =
        correctedWeight e ρ φ z + ((σ z - ρ z : ℝ) : EReal) := by
      simp only [correctedWeight]
      rw [add_assoc, ← EReal.coe_add]
      congr 2
      ring
    rw [hsplit, multiplierWeight_add_coe hmR, hare z hz]
    congr 3
    ring
  have hsup : ∀ y ∈ B, bergmanSup B (fun z => multiplierWeight m (correctedWeight e σ φ z)) y =
      ENNReal.ofReal (Real.exp ((m : ℝ) * (σ y - ρ y))) *
        bergmanSup B (fun z => multiplierWeight m (correctedWeight e ρ φ z)) y := by
    intro y hy
    rw [QuantitativeRegularizationSingularWeight.bergmanSup_congr_of_eqOn hBo.measurableSet
      hweight y, BergmanHolomorphicMultiplier.bergmanSup_exp_weight ha, hare y hy]
    congr 3
    ring
  rw [chartBergmanBranch_of_mem hx, chartBergmanBranch_of_mem hx, bergmanLog, bergmanLog,
    hsup _ hx.2, ENNReal.log_mul_add, ENNReal.log_ofReal_of_pos (Real.exp_pos _), Real.log_exp]
  exact inv_mul_coe_add_sub hmR _ _ _

end

end Hironaka.QuantitativeRegularizationChartBranch
