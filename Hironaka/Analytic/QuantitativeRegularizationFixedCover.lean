import Hironaka.Analytic.QuantitativeRegularizationChartOverlap
import Hironaka.Analytic.QuantitativeRegularizationMaxGluing
import Hironaka.Analytic.PrescribedBallPotentials

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Copy-4 `lem:regularization` on a fixed cover

Source: Copy-4, `lem:regularization`
(`references/transcendental-nakamaye-copy4-20260911/source/main-Nulllocus.tex:851-1060`);
blueprint `ana:regularization`.  Demailly, *Regularization of closed positive currents and
intersection theory*, J. Algebraic Geom. 1 (1992), Theorem 1.1, in the one-sided
multiplier-ideal form Copy-4 uses.

This module assembles the statement of `lem:regularization` from the proved pieces:

* **the fixed cover** (Copy-4 Step 1, "fix once and for all, depending only on `Z`"): around
  every point `p` the preferred chart `e_p`, a radius `R_p` with `ball (e_p p) R_p` inside the
  chart target, the potential radius `P_p = ddcRadius d R_p` of the quantitative local
  `ddᶜ`-lemma (`PrescribedBall.exists_smooth_ddc_potential_ball`), the Bergman ball
  `B_p = ball (e_p p) (P_p / 2)`, and a cut-off patch `U_p ⋐ V_p ⋐ e_p⁻¹(ball (e_p p) (P_p / 4))`
  (`IdealFunctionMaxGluing.exists_patch`); compactness keeps finitely many;
* **the overlap constant** (Step 2): for each pair `(j, l)`,
  `QuantitativeRegularizationChartOverlap.exists_const_overlapBound` on the compact
  `V̄_j ∩ V̄_l`; `C_B` is their sum, fixed before `ζ`;
* **the branches** (Steps 1 and 4): for a given `ζ` the quantitative `ddᶜ`-lemma gives a
  smooth potential `ρ_j` of `ζ` on the potential ball of every patch, and the branch is
  `QuantitativeRegularizationChartBranch.chartBergmanBranch (e_j) (B_j) ρ_j φ m`, which is
  `ζ`-PSH, nondegenerate and dominates every germ family of `𝓘(mφ)`;
* **the gluing** (Steps 3--4): `QuantitativeRegularizationMaxGluing.exists_regularization_of_branches`.

In dimension `0` the manifold is discrete, every form vanishes, and the trivial one-patch cover
with branch `φ` itself does the job (`exists_regularization_multiplierIdeal_lowerBound_dim_zero`).

## Main results

* `FixedChartCover`, `exists_fixedChartCover` — the fixed cover as data: the cut-off cover
  (with `0 ≤ χ_j ≤ 1`), the charts `e_j`, centres `c_j`, Bergman radii `β_j`, potential radii
  `P_j` and the overlap constant `C_B`, none depending on `ζ`, `φ` or `m`;
* `FixedChartCover.branch`, `FixedChartCover.branch_spec` — the branches
  `b_{m,j} = chartBergmanBranch (e_j) (ball c_j β_j) ρ_j φ m` for potentials `ρ_j` of `ζ` chosen
  once (`FixedChartCover.exists_potentials`), with the four branch properties at every level
  `m` (so that statements about the family `m ↦ b_{m,j}` can be proved about them);
* `exists_fixedCover_branches` — the branch data on a fixed cover (Steps 1, 2 and the germ half
  of Step 4), in the form both gluings consume (plain maximum here, `M_δ` in
  `DemaillySymmetricGluing`);
* `exists_regularization_multiplierIdeal_lowerBound` — the statement of
  `QuantitativeRegularization.demailly1992_exists_regularization_multiplierIdeal_lowerBound`
  (without the connectedness hypothesis, which is not used).
-/

open Set Filter Metric TopologicalSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.QuantitativeRegularizationFixedCover

open Hironaka.PositiveClasses Hironaka.HolomorphicIdealSheaves
  Hironaka.AnalyticGluingData Hironaka.MongeAmpere
  QuantitativeRegularizationChartBranch QuantitativeRegularizationChartOverlap
  QuantitativeRegularizationMaxGluing

noncomputable section

variable {d : ℕ} {Z : Type*} [TopologicalSpace Z]
  [ChartedSpace (ComplexModel d) Z] [IsComplexManifold d Z]

/-! ### Potentials of a closed `(1,1)`-form on a prescribed ball -/

/-- **A smooth potential of `ζ` on a prescribed ball of a chart**: if `ball c R` lies in the
target of `e`, then `ζ` has a smooth local potential on `ball c (ddcRadius d R)`, a radius
depending on `d` and `R` only. -/
theorem exists_isSmoothLocalPotential_ball (hd : d ≠ 0) (ζ : ClosedRealOneOneForm d Z)
    (e : ComplexChart d Z) {c : ComplexModel d} {R : ℝ} (hR : 0 < R)
    (hRe : ball c R ⊆ e.val.target) :
    ∃ ρ : ComplexModel d → ℝ,
      IsSmoothLocalPotential ζ.val e (ball c (PrescribedBall.ddcRadius d R)) ρ := by
  obtain ⟨ρ, hρ, hρeq⟩ := PrescribedBall.exists_smooth_ddc_potential_ball hd hR
    (ζ.val.coeff e) ((ζ.val.smooth e).mono hRe)
    (fun z hz => ζ.property.1 e z (hRe hz)) (fun z hz => ζ.property.2 e z (hRe hz))
  have hsub : ball c (PrescribedBall.ddcRadius d R) ⊆ ball c R :=
    ball_subset_ball ((PrescribedBall.ddcRadius_le_half hR.le).trans (by linarith))
  exact ⟨ρ, isOpen_ball, hsub.trans hRe, hρ.contDiffOn, hρeq⟩

/-! ### The fixed chart cover as data -/

/-- **The fixed chart cover of Copy-4 `lem:regularization`, Step 1, as data.**  A finite cut-off
cover `(U_j ⋐ V_j, χ_j)` with `0 ≤ χ_j ≤ 1`; for every patch a chart `e_j`, a centre `c_j`, a
Bergman radius `β_j > 0` and a potential radius `P_j > β_j`, such that `V̄_j` lies in the patch
`e_j⁻¹(ball c_j β_j)` of the Bergman ball `B_j = ball c_j β_j`; every closed real
`(1,1)`-form has a smooth potential on every potential ball `ball c_j P_j`; and ONE constant
`C_B ≥ 0` bounds every overlap `b_j ≤ b_l + C_B/m` on `V̄_j ∩ V̄_l` (`eq:reg-overlap`) for every
form, every pair of potentials, every quasi-psh `φ` and every `m ≥ 1`.  None of these data
depends on `ζ`, `φ` or `m`; the branches of `lem:regularization` are
`FixedChartCover.branch`. -/
structure FixedChartCover (d : ℕ) (Z : Type*) [TopologicalSpace Z]
    [ChartedSpace (ComplexModel d) Z] [IsComplexManifold d Z] where
  /-- The index set: the centres of the patches. -/
  t : Finset Z
  /-- The cut-off cover `(U_j ⋐ V_j, χ_j)`. -/
  cover : CutoffCover d Z t
  /-- The chart `e_j` of the `j`-th patch. -/
  chart : t → ComplexChart d Z
  /-- The centre `c_j` of the `j`-th chart balls. -/
  center : t → ComplexModel d
  /-- The radius `β_j` of the Bergman ball `B_j = ball c_j β_j`. -/
  bergmanRadius : t → ℝ
  /-- The radius `P_j` of the ball carrying the potentials. -/
  potentialRadius : t → ℝ
  /-- The overlap constant `C_B`. -/
  CB : ℝ
  CB_nonneg : 0 ≤ CB
  bergmanRadius_pos : ∀ j, 0 < bergmanRadius j
  bergmanRadius_lt_potentialRadius : ∀ j, bergmanRadius j < potentialRadius j
  χ_le_one : ∀ j y, cover.χ j y ≤ 1
  closure_V_subset_chartPatch :
    ∀ j, closure (cover.V j) ⊆ chartPatch (chart j) (ball (center j) (bergmanRadius j))
  exists_potential : ∀ (ζ : ClosedRealOneOneForm d Z) (j : t), ∃ ρ : ComplexModel d → ℝ,
    IsSmoothLocalPotential ζ.val (chart j) (ball (center j) (potentialRadius j)) ρ
  overlapBound : ∀ j l : t,
    OverlapBound (chart j) (chart l) (center j) (center l) (bergmanRadius j) (potentialRadius j)
      (bergmanRadius l) (potentialRadius l) (closure (cover.V j) ∩ closure (cover.V l)) CB

/-- **Copy-4 `lem:regularization`, Steps 1--2: the fixed chart cover exists** on a compact
complex manifold of positive dimension (preferred charts, `R_p`, `P_p = ddcRadius d R_p`,
`β_p = P_p/2`, patches in `e_p⁻¹(ball (P_p/4))`, a finite subcover, `C_B` = the sum of the pair
constants of `exists_const_overlapBound`). -/
theorem exists_fixedChartCover (hd : 0 < d) [CompactSpace Z] :
    Nonempty (FixedChartCover d Z) := by
  classical
  -- the chart data around every point
  let e : Z → ComplexChart d Z := fun p => complexChartAt (n := d) p
  let c : Z → ComplexModel d := fun p => (e p).val p
  have hcT : ∀ p, c p ∈ (e p).val.target := fun p =>
    (e p).val.map_source (mem_complexChartAt_source p)
  have hRex : ∀ p, ∃ R : ℝ, 0 < R ∧ ball (c p) R ⊆ (e p).val.target := fun p =>
    Metric.isOpen_iff.mp (e p).val.open_target (c p) (hcT p)
  choose R hR hRe using hRex
  let P : Z → ℝ := fun p => PrescribedBall.ddcRadius d (R p)
  have hP : ∀ p, 0 < P p := fun p => PrescribedBall.ddcRadius_pos (hR p)
  let β : Z → ℝ := fun p => P p / 2
  let γ : Z → ℝ := fun p => P p / 4
  have hβ : ∀ p, 0 < β p := fun p => by have := hP p; positivity
  have hβP : ∀ p, β p < P p := fun p => by have := hP p; simp only [β]; linarith
  have hγβ : ∀ p, γ p < β p := fun p => by have := hP p; simp only [β, γ]; linarith
  -- the cut-off patches
  have hpatch : ∀ p : Z, ∃ (U V : Set Z) (χ : Z → ℝ), IsOpen U ∧ IsOpen V ∧ p ∈ U ∧
      closure V ⊆ chartPatch (e p) (ball (c p) (γ p)) ∧ closure U ⊆ V ∧
      ChartSmooth (n := d) χ ∧ (∀ y, 0 ≤ χ y) ∧ (∀ y, χ y ≤ 1) ∧ (∀ y ∈ U, χ y = 1) ∧
      tsupport χ ⊆ V := fun p =>
    IdealFunctionMaxGluing.exists_patch (n := d) (isOpen_chartPatch (e p) isOpen_ball)
      ⟨mem_complexChartAt_source p, mem_ball_self (by have := hP p; positivity)⟩
  choose U V χ hU hV hpU hVG _hUV hχ hχ0 hχ1 hχU hχV using hpatch
  -- finitely many patches
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover U hU
    (fun x _ => mem_iUnion.mpr ⟨x, hpU x⟩)
  let cover : CutoffCover d Z t :=
    { V := fun j => V j.1
      isOpen_V := fun j => hV j.1
      U := fun j => U j.1
      isOpen_U := fun j => hU j.1
      cover := fun y => by
        obtain ⟨p, hp, hyp⟩ := mem_iUnion₂.mp (ht (mem_univ y))
        exact ⟨⟨p, hp⟩, hyp⟩
      χ := fun j => χ j.1
      χ_smooth := fun j => hχ j.1
      χ_nonneg := fun j => hχ0 j.1
      χ_eq_one := fun j => hχU j.1
      tsupport_χ_subset := fun j => hχV j.1 }
  -- the patch lies in the chart and in the Bergman ball
  have hVpatch : ∀ p, ∀ x ∈ closure (V p), x ∈ (e p).val.source ∧ (e p).val x ∈ ball (c p) (γ p) :=
    fun p x hx => hVG p hx
  -- the overlap constants, fixed before `ζ`
  have hpair : ∀ j l : t, ∃ C : ℝ, 0 ≤ C ∧
      OverlapBound (e j.1) (e l.1) (c j.1) (c l.1) (β j.1) (P j.1) (β l.1) (P l.1)
        (closure (V j.1) ∩ closure (V l.1)) C := fun j l =>
    exists_const_overlapBound hd (e j.1) (e l.1) (hβP j.1) (hβ l.1) (hβP l.1)
      (isClosed_closure.inter isClosed_closure).isCompact
      (fun x hx => by
        obtain ⟨h1, h2⟩ := hVpatch j.1 x hx.1
        exact ⟨h1, ball_subset_ball (hγβ j.1).le h2⟩)
      (fun x hx => by
        obtain ⟨h1, h2⟩ := hVpatch l.1 x hx.2
        exact ⟨h1, ball_subset_closedBall (ball_subset_ball (hγβ l.1).le h2)⟩)
  choose Cp hCp0 hCp using hpair
  set CB : ℝ := ∑ j : t, ∑ l : t, Cp j l with hCBdef
  have hCB : 0 ≤ CB := Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun l _ => hCp0 j l
  have hCpCB : ∀ j l, Cp j l ≤ CB := fun j l =>
    (Finset.single_le_sum (f := fun l => Cp j l) (fun l _ => hCp0 j l) (Finset.mem_univ l)).trans
      (Finset.single_le_sum (f := fun j => ∑ l : t, Cp j l)
        (fun j _ => Finset.sum_nonneg fun l _ => hCp0 j l) (Finset.mem_univ j))
  exact ⟨{
    t := t
    cover := cover
    chart := fun j => e j.1
    center := fun j => c j.1
    bergmanRadius := fun j => β j.1
    potentialRadius := fun j => P j.1
    CB := CB
    CB_nonneg := hCB
    bergmanRadius_pos := fun j => hβ j.1
    bergmanRadius_lt_potentialRadius := fun j => hβP j.1
    χ_le_one := fun j => hχ1 j.1
    closure_V_subset_chartPatch := fun j x hx => by
      obtain ⟨h1, h2⟩ := hVpatch j.1 x hx
      exact ⟨h1, ball_subset_ball (hγβ j.1).le h2⟩
    exists_potential := fun ζ j =>
      exists_isSmoothLocalPotential_ball hd.ne' ζ (e j.1) (hR j.1) (hRe j.1)
    overlapBound := fun j l ζ ρj ρl hρj hρl φ hφ m hm x hx hxl =>
      (hCp j l ζ ρj ρl hρj hρl φ hφ m hm x hx hxl).trans
        (add_coe_div_le_add_coe_div (hCpCB j l) (by exact_mod_cast hm)) }⟩

namespace FixedChartCover

variable (F : FixedChartCover d Z)

/-- **The branch `b_{m,j}` of `lem:regularization`** for the potentials `ρ_j` of `ζ`: the chart
Bergman branch `m⁻¹ log K_{B_j, e^{-m(φ ∘ e_j⁻¹ + ρ_j)}} ∘ e_j - ρ_j ∘ e_j` of the Bergman ball
`B_j = ball c_j β_j`.  The cover, the charts, the balls and the potentials are the same for
every `m`. -/
def branch (ρ : F.t → ComplexModel d → ℝ) (φ : Z → EReal) (m : ℕ) (j : F.t) : Z → EReal :=
  chartBergmanBranch (F.chart j) (ball (F.center j) (F.bergmanRadius j)) (ρ j) φ m

theorem V_subset_chartPatch (j : F.t) :
    F.cover.V j ⊆ chartPatch (F.chart j) (ball (F.center j) (F.bergmanRadius j)) :=
  subset_closure.trans (F.closure_V_subset_chartPatch j)

/-- `0 ≤ χ_j ≤ 1`. -/
theorem χ_mem_Icc (j : F.t) (y : Z) : F.cover.χ j y ∈ Icc (0 : ℝ) 1 :=
  ⟨F.cover.χ_nonneg j y, F.χ_le_one j y⟩

/-- The explicit form of the branch on the patch of its Bergman ball. -/
theorem branch_of_mem {ρ : F.t → ComplexModel d → ℝ} {φ : Z → EReal} {m : ℕ} {j : F.t} {x : Z}
    (hx : x ∈ chartPatch (F.chart j) (ball (F.center j) (F.bergmanRadius j))) :
    F.branch ρ φ m j x =
      (((m : ℝ)⁻¹ : ℝ) : EReal) *
          BergmanSupWeight.bergmanLog (ball (F.center j) (F.bergmanRadius j))
            (fun z => multiplierWeight m (correctedWeight (F.chart j) (ρ j) φ z))
            ((F.chart j).val x) -
        (ρ j ((F.chart j).val x) : EReal) :=
  chartBergmanBranch_of_mem hx

/-- One choice of potentials `ρ_j` of a closed real `(1,1)`-form `ζ` on the potential balls. -/
theorem exists_potentials (ζ : ClosedRealOneOneForm d Z) :
    ∃ ρ : F.t → ComplexModel d → ℝ, ∀ j,
      IsSmoothLocalPotential ζ.val (F.chart j) (ball (F.center j) (F.potentialRadius j)) (ρ j) := by
  choose ρ hρ using F.exists_potential ζ
  exact ⟨ρ, hρ⟩

variable {F}

/-- The corrected weight `φ ∘ e_j⁻¹ + ρ_j` is psh on the potential ball. -/
theorem plurisubharmonicOn_correctedWeight {ζ : SmoothRealForm d Z 2}
    {ρ : F.t → ComplexModel d → ℝ}
    (hρ : ∀ j, IsSmoothLocalPotential ζ (F.chart j) (ball (F.center j) (F.potentialRadius j)) (ρ j))
    {φ : Z → EReal} (hφ : ThetaPlurisubharmonic ζ φ) (j : F.t) :
    PlurisubharmonicOn (correctedWeight (F.chart j) (ρ j) φ)
      (ball (F.center j) (F.potentialRadius j)) :=
  QuantitativeRegularizationChartBranch.plurisubharmonicOn_correctedWeight hφ (hρ j)

/-- **`eq:reg-local-positivity`**: every branch is `ζ`-PSH on its patch `V_j`. -/
theorem thetaPlurisubharmonicOn_branch {ζ : SmoothRealForm d Z 2}
    {ρ : F.t → ComplexModel d → ℝ}
    (hρ : ∀ j, IsSmoothLocalPotential ζ (F.chart j) (ball (F.center j) (F.potentialRadius j)) (ρ j))
    {φ : Z → EReal} (hφ : ThetaPlurisubharmonic ζ φ) {m : ℕ} (hm : 0 < m) (j : F.t) :
    ThetaPlurisubharmonicOn ζ (F.branch ρ φ m j) (F.cover.V j) := by
  intro e' z hz hzV
  exact thetaPlurisubharmonicOn_chartBergmanBranch hφ (hρ j) isOpen_ball
    isBounded_ball.isCompact_closure
    (closure_ball_subset_closedBall.trans
      (closedBall_subset_ball (F.bergmanRadius_lt_potentialRadius j))) hm
    e' z hz (F.V_subset_chartPatch j hzV)

/-- **`eq:reg-overlap`**: `b_{m,j} ≤ b_{m,l} + C_B/m` on `V_j ∩ V_l`. -/
theorem branch_le_branch_add {ζ : SmoothRealForm d Z 2} {ρ : F.t → ComplexModel d → ℝ}
    (hρ : ∀ j, IsSmoothLocalPotential ζ (F.chart j) (ball (F.center j) (F.potentialRadius j)) (ρ j))
    {φ : Z → EReal} (hφ : ThetaPlurisubharmonic ζ φ) {m : ℕ} (hm : 0 < m) (j l : F.t) {y : Z}
    (hy : y ∈ F.cover.V j ∩ F.cover.V l) :
    F.branch ρ φ m j y ≤ F.branch ρ φ m l y + ((F.CB / (m : ℝ) : ℝ) : EReal) :=
  F.overlapBound j l ζ (ρ j) (ρ l) (hρ j) (hρ l) φ hφ m hm y
    ⟨subset_closure hy.1, subset_closure hy.2⟩ (F.V_subset_chartPatch l hy.2)

/-- **Nondegeneracy**: a branch is `-∞` on no neighbourhood of a point of its patch. -/
theorem exists_ne_bot_branch {ζ : SmoothRealForm d Z 2} {ρ : F.t → ComplexModel d → ℝ}
    (hρ : ∀ j, IsSmoothLocalPotential ζ (F.chart j) (ball (F.center j) (F.potentialRadius j)) (ρ j))
    {φ : Z → EReal} (hφ : IsThetaPshPotential ζ φ) {m : ℕ} (hm : 0 < m) (j : F.t) {x : Z}
    (hx : x ∈ F.cover.V j) {O : Set Z} (hO : IsOpen O) (hxO : x ∈ O) :
    ∃ y ∈ O, F.branch ρ φ m j y ≠ ⊥ :=
  exists_ne_bot_chartBergmanBranch hφ (hρ j) isOpen_ball (convex_ball _ _) isBounded_ball
    (ball_subset_ball (F.bergmanRadius_lt_potentialRadius j).le) hm (F.V_subset_chartPatch j hx)
    hO hxO

/-- **Copy-4 `lem:regularization`, Step 4, on the fixed cover**: near every point of a patch,
`m⁻¹ log ∑ᵢ |gᵢ|² - C ≤ b_{m,j}` for every finite family `g` of germs of `𝓘(mφ)`. -/
theorem exists_const_eventually_le_branch (hd : 0 < d) {ζ : SmoothRealForm d Z 2}
    {ρ : F.t → ComplexModel d → ℝ}
    (hρ : ∀ j, IsSmoothLocalPotential ζ (F.chart j) (ball (F.center j) (F.potentialRadius j)) (ρ j))
    {φ : Z → EReal} (hφ : ThetaPlurisubharmonic ζ φ) {m : ℕ} (hm : 0 < m) (j : F.t) {x : Z}
    (hx : x ∈ F.cover.V j) {N : ℕ} {g : Fin N → Z → ℂ}
    (hg : ∀ i, (multiplierIdeal (n := d) (m : ℝ) φ).mem x (g i)) :
    ∃ C : ℝ, ∀ᶠ y in 𝓝 x,
      (((m : ℝ)⁻¹ : ℝ) : EReal) * generatorLog g y - (C : EReal) ≤ F.branch ρ φ m j y := by
  have hβP := F.bergmanRadius_lt_potentialRadius j
  let A : Opens (ComplexModel d) :=
    ⟨ball (F.center j) ((F.bergmanRadius j + F.potentialRadius j) / 2), isOpen_ball⟩
  let Ω : Opens (ComplexModel d) := ⟨ball (F.center j) (F.potentialRadius j), isOpen_ball⟩
  have hβA : F.bergmanRadius j < (F.bergmanRadius j + F.potentialRadius j) / 2 := by linarith
  have hAP : (F.bergmanRadius j + F.potentialRadius j) / 2 < F.potentialRadius j := by linarith
  have hAΩ : RelativelyCompactIn A Ω :=
    ⟨isBounded_ball.isCompact_closure,
      closure_ball_subset_closedBall.trans (closedBall_subset_ball hAP)⟩
  exact exists_const_eventually_le_chartBergmanBranch hd hφ (A := A) (Ω := Ω)
    (convex_ball _ _) hAΩ (hρ j) isOpen_ball isBounded_ball.isCompact_closure
    (closure_ball_subset_closedBall.trans (closedBall_subset_ball hβA)) hm
    (F.V_subset_chartPatch j hx) hg

/-- **The four branch properties on the fixed cover**, for the SAME cover, charts, balls and
potentials at every level `m`: exactly the hypothesis of
`QuantitativeRegularizationMaxGluing.exists_regularization_of_branches` and of
`DemaillySymmetricGluing.exists_regularization_of_branches_rmax`, with `b = F.branch ρ φ m`. -/
theorem branch_spec (hd : 0 < d) {ζ : SmoothRealForm d Z 2} {ρ : F.t → ComplexModel d → ℝ}
    (hρ : ∀ j, IsSmoothLocalPotential ζ (F.chart j) (ball (F.center j) (F.potentialRadius j)) (ρ j))
    {φ : Z → EReal} (hφ : IsThetaPshPotential ζ φ) {m : ℕ} (hm : 1 ≤ m) :
    (∀ j, ThetaPlurisubharmonicOn ζ (F.branch ρ φ m j) (F.cover.V j)) ∧
    (∀ j l, ∀ y ∈ F.cover.V j ∩ F.cover.V l,
      F.branch ρ φ m j y ≤ F.branch ρ φ m l y + ((F.CB / (m : ℝ) : ℝ) : EReal)) ∧
    (∀ j, ∀ x ∈ F.cover.U j, ∀ O : Set Z, IsOpen O → x ∈ O → ∃ y ∈ O, F.branch ρ φ m j y ≠ ⊥) ∧
    (∀ j, ∀ x ∈ F.cover.U j, ∀ (N : ℕ) (g : Fin N → Z → ℂ),
      (∀ i, (multiplierIdeal (n := d) (m : ℝ) φ).mem x (g i)) →
      ∃ C : ℝ, ∀ᶠ y in 𝓝 x,
        (((m : ℝ)⁻¹ : ℝ) : EReal) * generatorLog g y - (C : EReal) ≤ F.branch ρ φ m j y) := by
  have hm0 : 0 < m := hm
  exact ⟨thetaPlurisubharmonicOn_branch hρ hφ.1 hm0,
    fun j l y hy => branch_le_branch_add hρ hφ.1 hm0 j l hy,
    fun j x hx O hO hxO =>
      exists_ne_bot_branch hρ hφ hm0 j (F.cover.U_subset_V j hx) hO hxO,
    fun j x hx _ _ hg =>
      exists_const_eventually_le_branch hd hρ hφ.1 hm0 j (F.cover.U_subset_V j hx) hg⟩

end FixedChartCover

/-! ### Positive dimension -/

/-- **Copy-4 `lem:regularization`, Steps 1--2 and the germ half of Step 4: branch data on a
fixed cover.**  In positive dimension, a finite cut-off cover and a constant `C_B ≥ 0`, both
fixed before `ζ`, carry for every `ζ`, every `φ ∈ PSH(Z, ζ)` and every `m ≥ 1` branches that are
`ζ`-PSH on their patches, satisfy `b_j ≤ b_l + C_B/m` on overlaps, are `-∞` on no neighbourhood
of a point of their cores, and dominate `m⁻¹ log ∑|gᵢ|²` near every point of their cores for
every finite family of germs of `𝓘(mφ)`.  This is exactly the hypothesis of
`QuantitativeRegularizationMaxGluing.exists_regularization_of_branches` (plain maximum) and of
`DemaillySymmetricGluing.exists_regularization_of_branches_rmax` (Demailly's `M_δ`).  The
branches are the chart Bergman branches
`QuantitativeRegularizationChartBranch.chartBergmanBranch (e_j) (B_j) ρ_j φ m`. -/
theorem exists_fixedCover_branches (hd : 0 < d) [CompactSpace Z] :
    ∃ (t : Finset Z) (P : CutoffCover d Z t) (CB : ℝ), 0 ≤ CB ∧
      ∀ (ζ : ClosedRealOneOneForm d Z) (φ : Z → EReal),
        IsThetaPshPotential ζ.val φ → ∀ m : ℕ, 1 ≤ m →
          ∃ b : t → Z → EReal,
            (∀ j, ThetaPlurisubharmonicOn ζ.val (b j) (P.V j)) ∧
            (∀ j l, ∀ y ∈ P.V j ∩ P.V l, b j y ≤ b l y + ((CB / (m : ℝ) : ℝ) : EReal)) ∧
            (∀ j, ∀ x ∈ P.U j, ∀ O : Set Z, IsOpen O → x ∈ O → ∃ y ∈ O, b j y ≠ ⊥) ∧
            (∀ j, ∀ x ∈ P.U j, ∀ (N : ℕ) (g : Fin N → Z → ℂ),
              (∀ i, (multiplierIdeal (n := d) (m : ℝ) φ).mem x (g i)) →
              ∃ C : ℝ, ∀ᶠ y in 𝓝 x,
                (((m : ℝ)⁻¹ : ℝ) : EReal) * generatorLog g y - (C : EReal) ≤ b j y) := by
  obtain ⟨F⟩ := exists_fixedChartCover (Z := Z) hd
  refine ⟨F.t, F.cover, F.CB, F.CB_nonneg, fun ζ φ hφ m hm => ?_⟩
  obtain ⟨ρ, hρ⟩ := F.exists_potentials ζ
  exact ⟨F.branch ρ φ m, F.branch_spec hd hρ hφ hm⟩

/-- **Copy-4 `lem:regularization` in positive dimension**: the branch data on the fixed cover
(`exists_fixedCover_branches`), glued by the plain maximum. -/
theorem exists_regularization_multiplierIdeal_lowerBound_of_pos (hd : 0 < d) [CompactSpace Z]
    (omegaZ : KahlerBackground d Z) :
    ∃ c : ℝ, 0 < c ∧
      ∀ (ζ : ClosedRealOneOneForm d Z) (φ : Z → EReal),
        IsThetaPshPotential ζ.val φ →
        ∀ m : ℕ, 1 ≤ m →
          ∃ φm : Z → EReal,
            IsThetaPshPotential (ζ + (c / (m : ℝ)) • omegaZ.form).val φm ∧
            ∀ (x : Z) (N : ℕ) (g : Fin N → Z → ℂ),
              (∀ i, (multiplierIdeal (n := d) (m : ℝ) φ).mem x (g i)) →
              ∃ C : ℝ, ∀ᶠ y in 𝓝 x,
                (((m : ℝ)⁻¹ : ℝ) : EReal) * generatorLog g y - (C : EReal) ≤ φm y := by
  obtain ⟨t, P, CB, hCB, hbranch⟩ := exists_fixedCover_branches (Z := Z) hd
  exact exists_regularization_of_branches omegaZ P hCB hbranch

/-! ### Dimension zero -/

/-- `a - (a.toReal - b.toReal) ≤ b` for `a ≠ ⊤` and `b ≠ ⊥`. -/
theorem sub_toReal_sub_toReal_le {a b : EReal} (ha : a ≠ ⊤) (hb : b ≠ ⊥) :
    a - ((a.toReal - b.toReal : ℝ) : EReal) ≤ b := by
  induction a using EReal.rec with
  | bot => rw [EReal.bot_sub]; exact bot_le
  | top => exact absurd rfl ha
  | coe s =>
      induction b using EReal.rec with
      | bot => exact absurd rfl hb
      | top => exact le_top
      | coe t =>
          rw [EReal.toReal_coe, EReal.toReal_coe, ← EReal.coe_sub, EReal.coe_le_coe_iff]
          linarith

/-- In dimension `0` every point is open. -/
theorem isOpen_singleton_of_dim_zero {Y : Type*} [TopologicalSpace Y]
    [ChartedSpace (ComplexModel 0) Y] (x : Y) : IsOpen ({x} : Set Y) := by
  have hsub : ∀ a b : ComplexModel 0, a = b := fun a b => by
    ext i
    exact i.elim0
  have heq : (chartAt (ComplexModel 0) x).source = {x} := by
    ext y
    refine ⟨fun hy => ?_, fun hy => ?_⟩
    · exact (chartAt (ComplexModel 0) x).injOn hy (mem_chart_source (ComplexModel 0) x)
        (hsub _ _)
    · rw [mem_singleton_iff.mp hy]
      exact mem_chart_source (ComplexModel 0) x
  rw [← heq]
  exact (chartAt (ComplexModel 0) x).open_source

/-- **Copy-4 `lem:regularization` in dimension `0`**: the one-patch cover with branch `φ`. -/
theorem exists_regularization_multiplierIdeal_lowerBound_dim_zero {Y : Type*}
    [TopologicalSpace Y] [ChartedSpace (ComplexModel 0) Y] [IsComplexManifold 0 Y]
    [CompactSpace Y] (omegaZ : KahlerBackground 0 Y) :
    ∃ c : ℝ, 0 < c ∧
      ∀ (ζ : ClosedRealOneOneForm 0 Y) (φ : Y → EReal),
        IsThetaPshPotential ζ.val φ →
        ∀ m : ℕ, 1 ≤ m →
          ∃ φm : Y → EReal,
            IsThetaPshPotential (ζ + (c / (m : ℝ)) • omegaZ.form).val φm ∧
            ∀ (x : Y) (N : ℕ) (g : Fin N → Y → ℂ),
              (∀ i, (multiplierIdeal (n := 0) (m : ℝ) φ).mem x (g i)) →
              ∃ C : ℝ, ∀ᶠ y in 𝓝 x,
                (((m : ℝ)⁻¹ : ℝ) : EReal) * generatorLog g y - (C : EReal) ≤ φm y := by
  let cover : CutoffCover 0 Y Unit :=
    { V := fun _ => univ
      isOpen_V := fun _ => isOpen_univ
      U := fun _ => univ
      isOpen_U := fun _ => isOpen_univ
      cover := fun _ => ⟨(), trivial⟩
      χ := fun _ _ => 1
      χ_smooth := fun _ _ => contDiffOn_const
      χ_nonneg := fun _ _ => zero_le_one
      χ_eq_one := fun _ _ _ => rfl
      tsupport_χ_subset := fun _ => subset_univ _ }
  refine exists_regularization_of_branches omegaZ cover le_rfl ?_
  intro ζ φ hφ m hm
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  refine ⟨fun _ => φ, fun _ e z hz _ => hφ.1 e z hz, fun _ _ y _ => ?_,
    fun _ x _ O hO hxO => hφ.2 x O hO hxO, fun _ x _ N g _ => ?_⟩
  · rw [zero_div, EReal.coe_zero, add_zero]
  · have hx : IsOpen ({x} : Set Y) := isOpen_singleton_of_dim_zero x
    have hφx : φ x ≠ ⊥ := by
      obtain ⟨y, hy, hyφ⟩ := hφ.2 x {x} hx rfl
      rwa [mem_singleton_iff.mp hy] at hyφ
    have hgx : (((m : ℝ)⁻¹ : ℝ) : EReal) * generatorLog g x ≠ ⊤ := by
      have hlog : generatorLog g x ≠ ⊤ := by
        simp only [generatorLog, logNormSq, ne_eq, ENNReal.log_eq_top_iff]
        exact ENNReal.ofReal_ne_top
      induction h : generatorLog g x using EReal.rec with
      | bot => rw [EReal.coe_mul_bot_of_pos (inv_pos.mpr hmR)]; exact bot_ne_top
      | top => exact absurd h hlog
      | coe s => rw [← EReal.coe_mul]; exact EReal.coe_ne_top _
    refine ⟨((((m : ℝ)⁻¹ : ℝ) : EReal) * generatorLog g x).toReal - (φ x).toReal, ?_⟩
    filter_upwards [hx.mem_nhds rfl] with y hy
    rw [mem_singleton_iff.mp hy]
    exact sub_toReal_sub_toReal_le hgx hφx

/-! ### The statement of `lem:regularization` -/

/-- **Copy-4 `lem:regularization`** (Demailly 1992, Theorem 1.1, one-sided multiplier-ideal
form): the statement of
`QuantitativeRegularization.demailly1992_exists_regularization_multiplierIdeal_lowerBound`,
proved; connectedness of `Z` is not used. -/
theorem exists_regularization_multiplierIdeal_lowerBound [CompactSpace Z]
    (omegaZ : KahlerBackground d Z) :
    ∃ c : ℝ, 0 < c ∧
      ∀ (ζ : ClosedRealOneOneForm d Z) (φ : Z → EReal),
        IsThetaPshPotential ζ.val φ →
        ∀ m : ℕ, 1 ≤ m →
          ∃ φm : Z → EReal,
            IsThetaPshPotential (ζ + (c / (m : ℝ)) • omegaZ.form).val φm ∧
            ∀ (x : Z) (N : ℕ) (g : Fin N → Z → ℂ),
              (∀ i, (multiplierIdeal (n := d) (m : ℝ) φ).mem x (g i)) →
              ∃ C : ℝ, ∀ᶠ y in 𝓝 x,
                (((m : ℝ)⁻¹ : ℝ) : EReal) * generatorLog g y - (C : EReal) ≤ φm y := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · exact exists_regularization_multiplierIdeal_lowerBound_dim_zero omegaZ
  · exact exists_regularization_multiplierIdeal_lowerBound_of_pos hd omegaZ

end

end Hironaka.QuantitativeRegularizationFixedCover
