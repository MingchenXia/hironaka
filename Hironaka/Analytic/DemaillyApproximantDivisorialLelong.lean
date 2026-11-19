import Hironaka.Analytic.DivisorialChangeOfVariables
import Hironaka.Analytic.LelongNumberChartTransport
import Hironaka.Analytic.LelongNumberComparison
import Hironaka.Analytic.GlobalPotentialPullback
import Hironaka.Analytic.HolomorphicPullback
import Hironaka.MarkedIdeal.InvertibleIdealQuotient
import Hironaka.Analytic.GlobalAnalyticSingularities
import Hironaka.Analytic.QuasiEquisingularApproximation
import Hironaka.Analytic.PotentialTheory.LocalPshDiscControl
import Hironaka.Analytic.LelongNumberPole

set_option autoImplicit false

/-!
# Divisorial Lelong numbers of the Demailly approximants

Blueprint `pc:divisorial-lelong`, `pc:divisorial-multiplier-order` and
`pc:demailly-divisorial-lelong` (Copy-4 `lem:domination`, Step 1; the valuative estimate of
Boucksom--Favre--Jonsson for Demailly's approximants), in the project's normalization of Lelong
numbers, `ν(log ‖z‖, 0) = 1`.  Assignment of TN23 to TN3 (I-0765).

Let `π : Y → Z` be a holomorphic map of complex manifolds of dimension `m + 1`, injective off a set
that is null in every preferred chart (`IsInjectiveOffNull`; a modification is injective off its
exceptional locus), `E ⊆ Y` a smooth hypersurface, `v` a `θ`-plurisubharmonic function on `Z`, and
`φ` a function with analytic singularities of type `(q⁻¹, 𝓘(q v))` (Demailly's approximant at
level `q = 2^k`).  Then

  `ν(π^* v, E) - 2A/q ≤ ν(π^* φ, E)`,

where `ν(u, E) = inf_{x ∈ E} ν(u, x)` (`divisorialLelongNumber`) and `A` bounds the log
discrepancy `A_E = 1 + ord_E (J_π)` along `E` (`LogDiscrepancyLE`); if moreover `v ≤ φ`, then
`ν(π^* φ, E) ≤ ν(π^* v, E)`.

* `DivisorFlattening E x`: the preferred chart at `x` followed by a biholomorphism `Φ` taking `E`
  to the hyperplane `{z_{m+1} = 0}` near `x` (the data of `RegularAtDim E x m`).
* `flatCoordMap π Φ`: `π` read in these coordinates and the preferred chart at `π x`;
  `LogDiscrepancyLE π E x A`: its complex Jacobian is `z_{m+1}^k J'` near `0`, with `J'` not
  identically zero on the hyperplane and `k + 1 ≤ A`.
* `exists_slice_bound`: the slice bound for `π^* v` in flattening coordinates, for every exponent
  below `ν(π^* v, E)` (`DivisorialSliceBound`, with Lelong numbers transported by
  `LelongNumberComparison.lelongNumber_le_comp`).
* `ofReal_sub_le_lelongNumber_comp`: the pointwise estimate at `x ∈ E`.
* `divisorialLelongNumber_comp_sub_le`, `divisorialLelongNumber_comp_le_of_le`: the two
  inequalities along `E`;
  `exists_quasiEquisingularApproximation_divisorialLelongNumber`: both, for the terms of Demailly's
  quasi-equisingular approximation (`QuasiEquisingularApproximationDemailly`).

Sorry-free.
-/

open Set Filter Metric MeasureTheory
open scoped Topology ENNReal NNReal Manifold ContDiff

namespace Hironaka.DemaillyApproximantDivisorialLelong

open Hironaka.NonKahlerLocus Hironaka.HolomorphicMaps
  Hironaka.HolomorphicIdealSheaves Hironaka.GlobalAnalyticSingularities
  DivisorialSliceBound DivisorialChangeOfVariables

noncomputable section

variable {m : ℕ} {Y : Type*} [TopologicalSpace Y] [ChartedSpace (ComplexModel (m + 1)) Y]
  [IsComplexManifold (m + 1) Y]
  {Z : Type*} [TopologicalSpace Z] [ChartedSpace (ComplexModel (m + 1)) Z]
  [IsComplexManifold (m + 1) Z]

/-! ### Definitions -/

omit [IsComplexManifold (m + 1) Y] in
variable (m) in
/-- **The divisorial Lelong number** `ν(u, E) = inf_{x ∈ E} ν(u, x)` (`pc:divisorial-lelong`). -/
def divisorialLelongNumber (u : Y → EReal) (E : Set Y) : ℝ≥0∞ :=
  ⨅ x ∈ E, lelongNumber (n := m + 1) u x

omit [IsComplexManifold (m + 1) Y] in
theorem divisorialLelongNumber_le {u : Y → EReal} {E : Set Y} {x : Y} (hx : x ∈ E) :
    divisorialLelongNumber m u E ≤ lelongNumber (n := m + 1) u x :=
  iInf₂_le (f := fun y (_ : y ∈ E) => lelongNumber (n := m + 1) u y) x hx

/-- **A flattening of `E` at `x`**: a biholomorphism `Φ` of a neighbourhood of `e x` in the
preferred chart `e` at `x` onto a neighbourhood of `0`, with `Φ (e x) = 0`, taking `E` to the
hyperplane `{z_{m+1} = 0}`.  This is the data of `RegularAtDim E x m`. -/
structure DivisorFlattening (E : Set Y) (x : Y) where
  Φ : LocalHolomorphicEquivAt (n := m + 1) ((complexChartAt (n := m + 1) x).val x)
  source_subset : Φ.source ⊆ (complexChartAt (n := m + 1) x).val.target
  map_center : Φ.toFun ((complexChartAt (n := m + 1) x).val x) = 0
  mem_iff : ∀ y ∈ (complexChartAt (n := m + 1) x).val.source,
    (complexChartAt (n := m + 1) x).val y ∈ Φ.source →
      (y ∈ E ↔ Φ.toFun ((complexChartAt (n := m + 1) x).val y) (Fin.last m) = 0)

namespace DivisorFlattening

variable {E : Set Y} {x : Y} (Φ : DivisorFlattening (m := m) E x)

/-- The point of `Y` with flattening coordinates `z`. -/
def point (z : ComplexModel (m + 1)) : Y :=
  (complexChartAt (n := m + 1) x).val.symm (Φ.Φ.invFun z)

/-- The flattening coordinates of a point of `Y`. -/
def coord (y : Y) : ComplexModel (m + 1) :=
  Φ.Φ.toFun ((complexChartAt (n := m + 1) x).val y)

omit [IsComplexManifold (m + 1) Y] in
theorem chart_mem_source : (complexChartAt (n := m + 1) x).val x ∈ Φ.Φ.source :=
  Φ.Φ.center_mem_source

omit [IsComplexManifold (m + 1) Y] in
theorem invFun_zero : Φ.Φ.invFun 0 = (complexChartAt (n := m + 1) x).val x := by
  rw [← Φ.map_center, Φ.Φ.left_inv _ Φ.chart_mem_source]

omit [IsComplexManifold (m + 1) Y] in
theorem zero_mem_target : (0 : ComplexModel (m + 1)) ∈ Φ.Φ.target := by
  rw [← Φ.map_center]; exact Φ.Φ.mapsTo_toFun Φ.chart_mem_source

omit [IsComplexManifold (m + 1) Y] in
theorem invFun_mem_target {z : ComplexModel (m + 1)} (hz : z ∈ Φ.Φ.target) :
    Φ.Φ.invFun z ∈ (complexChartAt (n := m + 1) x).val.target :=
  Φ.source_subset (Φ.Φ.mapsTo_invFun hz)

omit [IsComplexManifold (m + 1) Y] in
theorem point_mem_source {z : ComplexModel (m + 1)} (hz : z ∈ Φ.Φ.target) :
    Φ.point z ∈ (complexChartAt (n := m + 1) x).val.source :=
  (complexChartAt (n := m + 1) x).val.map_target (Φ.invFun_mem_target hz)

omit [IsComplexManifold (m + 1) Y] in
theorem chart_point {z : ComplexModel (m + 1)} (hz : z ∈ Φ.Φ.target) :
    (complexChartAt (n := m + 1) x).val (Φ.point z) = Φ.Φ.invFun z :=
  (complexChartAt (n := m + 1) x).val.right_inv (Φ.invFun_mem_target hz)

omit [IsComplexManifold (m + 1) Y] in
theorem coord_point {z : ComplexModel (m + 1)} (hz : z ∈ Φ.Φ.target) :
    Φ.coord (Φ.point z) = z := by
  rw [coord, Φ.chart_point hz, Φ.Φ.right_inv z hz]

omit [IsComplexManifold (m + 1) Y] in
theorem point_zero : Φ.point 0 = x := by
  rw [point, Φ.invFun_zero, (complexChartAt (n := m + 1) x).val.left_inv
    (mem_complexChartAt_source x)]

omit [IsComplexManifold (m + 1) Y] in
theorem coord_x : Φ.coord x = 0 := Φ.map_center

omit [IsComplexManifold (m + 1) Y] in
/-- Points of the hyperplane are points of `E`. -/
theorem point_mem {z : ComplexModel (m + 1)} (hz : z ∈ Φ.Φ.target) (hl : z (Fin.last m) = 0) :
    Φ.point z ∈ E := by
  refine (Φ.mem_iff _ (Φ.point_mem_source hz) ?_).mpr ?_
  · rw [Φ.chart_point hz]; exact Φ.Φ.mapsTo_invFun hz
  · rw [Φ.chart_point hz, Φ.Φ.right_inv z hz]; exact hl

omit [IsComplexManifold (m + 1) Y] in
/-- Near `x`, the point with the coordinates of `y` is `y`. -/
theorem eventually_point_coord : ∀ᶠ y in 𝓝 x, Φ.point (Φ.coord y) = y := by
  have hcont : ContinuousAt (complexChartAt (n := m + 1) x).val x :=
    (complexChartAt (n := m + 1) x).val.continuousAt (mem_complexChartAt_source x)
  filter_upwards [(complexChartAt (n := m + 1) x).val.open_source.mem_nhds
      (mem_complexChartAt_source x),
    hcont.eventually (Φ.Φ.isOpen_source.mem_nhds Φ.chart_mem_source)] with y hy hyΦ
  rw [point, coord, Φ.Φ.left_inv _ hyΦ, (complexChartAt (n := m + 1) x).val.left_inv hy]

omit [IsComplexManifold (m + 1) Y] in
theorem contDiffOn_invFun : ContDiffOn ℂ ∞ Φ.Φ.invFun Φ.Φ.target :=
  (HolomorphicAnalytic.analyticOnNhd_of_differentiableOn Φ.Φ.isOpen_target
    Φ.Φ.invFun_holomorphic).contDiffOn Φ.Φ.isOpen_target.uniqueDiffOn

theorem mdifferentiableAt_point {z : ComplexModel (m + 1)} (hz : z ∈ Φ.Φ.target) :
    MDifferentiableAt 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel (m + 1)) Φ.point z := by
  have hinv : MDifferentiableAt 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel (m + 1))
      Φ.Φ.invFun z :=
    (Φ.Φ.invFun_holomorphic.differentiableAt (Φ.Φ.isOpen_target.mem_nhds hz)).mdifferentiableAt
  have hsymm : MDifferentiableAt 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel (m + 1))
      (chartAt (ComplexModel (m + 1)) x).symm (Φ.Φ.invFun z) :=
    ((contMDiffOn_chart_symm (I := 𝓘(ℂ, ComplexModel (m + 1))) (n := ∞) (x := x)).contMDiffAt
      ((chartAt (ComplexModel (m + 1)) x).open_target.mem_nhds
        (Φ.invFun_mem_target hz))).mdifferentiableAt (by simp)
  exact hsymm.comp z hinv

theorem mdifferentiableAt_coord :
    MDifferentiableAt 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel (m + 1)) Φ.coord x := by
  have hchart : MDifferentiableAt 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel (m + 1))
      (chartAt (ComplexModel (m + 1)) x) x :=
    ((contMDiffOn_chart (I := 𝓘(ℂ, ComplexModel (m + 1))) (n := ∞) (x := x)).contMDiffAt
      ((chartAt (ComplexModel (m + 1)) x).open_source.mem_nhds
        (mem_chart_source _ x))).mdifferentiableAt (by simp)
  have hΦ : MDifferentiableAt 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel (m + 1))
      Φ.Φ.toFun ((chartAt (ComplexModel (m + 1)) x) x) :=
    (Φ.Φ.toFun_holomorphic.differentiableAt
      (Φ.Φ.isOpen_source.mem_nhds Φ.chart_mem_source)).mdifferentiableAt
  exact hΦ.comp x hchart

omit [IsComplexManifold (m + 1) Y] in
/-- A point where `E` is regular of dimension `m` (`RegularAtDim E x m`, the project's notion of a
smooth hypersurface point) carries a flattening. -/
theorem nonempty_of_regularAtDim {E : Set Y} {x : Y} (h : RegularAtDim (n := m + 1) E x m) :
    Nonempty (DivisorFlattening (m := m) E x) := by
  obtain ⟨-, -, Φ, hsub, hcenter, hmem⟩ := h
  refine ⟨⟨Φ, hsub, hcenter, fun y hy hyΦ => ?_⟩⟩
  rw [hmem hy hyΦ]
  constructor
  · intro hz; exact hz (Fin.last m) le_rfl
  · intro hz i hi
    have : i = Fin.last m := Fin.ext (le_antisymm (Nat.lt_succ_iff.mp i.2) hi)
    rw [this]; exact hz

end DivisorFlattening

/-! ### The slice bound for `π^* v` in flattening coordinates -/

/-- **Slice bound for `π^* v`** (`pc:divisorial-multiplier-order`, first step).  If `v` is
`θ`-plurisubharmonic and `r < ν(π^* v, E)`, then in flattening coordinates at `x ∈ E`, for every
`γ < r`, `v ∘ π ≤ γ log |z_{m+1}| + C` near `0` off the hyperplane. -/
theorem exists_slice_bound {π : Y → Z}
    (hπ : ContMDiff 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel (m + 1)) ∞ π)
    {θ : SmoothRealForm (m + 1) Z 2} {v : Z → EReal} (hv : ThetaPlurisubharmonic θ v)
    {E : Set Y} {x : Y} (Φ : DivisorFlattening (m := m) E x) {r : ℝ≥0}
    (hr : (r : ℝ≥0∞) < divisorialLelongNumber m (fun y => v (π y)) E) :
    ∀ γ < (r : ℝ), ∃ U ∈ 𝓝 (0 : ComplexModel (m + 1)), ∃ C : ℝ, ∀ z ∈ U,
      z (Fin.last m) ≠ 0 →
        v (π (Φ.point z)) ≤ ((γ * Real.log ‖z (Fin.last m)‖ + C : ℝ) : EReal) := by
  set u' : ComplexModel (m + 1) → EReal := fun z => v (π (Φ.point z)) with hu'
  have hvπ := GlobalPotentialPullback.thetaPlurisubharmonic_comp hπ hv
  -- the local plurisubharmonic model at `0`
  have hq : QuasiPlurisubharmonicAt u' 0 := by
    have h0 := hvπ.quasiPlurisubharmonic (complexChartAt (n := m + 1) x) (Φ.Φ.invFun 0)
      (Φ.invFun_mem_target Φ.zero_mem_target)
    exact HolomorphicPullback.quasiPlurisubharmonicAt_comp_holomorphic Φ.Φ.isOpen_target
      Φ.contDiffOn_invFun Φ.zero_mem_target h0
  obtain ⟨P, h, ⟨UP, hUPo, h0UP, hPdisc⟩, hh, heq⟩ := hq
  have hPpsh : PlurisubharmonicOn P UP := hPdisc.plurisubharmonicOn hUPo
  have hev : ∀ᶠ z in 𝓝 (0 : ComplexModel (m + 1)),
      (z ∈ UP ∧ u' z = P z + (h z : EReal)) ∧ (ContDiffAt ℝ ∞ h z ∧ z ∈ Φ.Φ.target) :=
    ((show ∀ᶠ z in 𝓝 (0 : ComplexModel (m + 1)), z ∈ UP from hUPo.mem_nhds h0UP).and heq).and (hh.and (Φ.Φ.isOpen_target.mem_nhds Φ.zero_mem_target))
  obtain ⟨R₀, hR₀, hball⟩ := Metric.mem_nhds_iff.mp hev
  -- a bound for `h` on `closedBall 0 (R₀ / 2)`
  have hsub2 : closedBall (0 : ComplexModel (m + 1)) (R₀ / 2) ⊆ ball 0 R₀ :=
    closedBall_subset_ball (by linarith)
  have hhcont : ContinuousOn h (closedBall (0 : ComplexModel (m + 1)) (R₀ / 2)) := fun z hz =>
    ((hball (hsub2 hz)).2.1.continuousAt).continuousWithinAt
  obtain ⟨Mh, hMh⟩ := (isCompact_closedBall (0 : ComplexModel (m + 1)) (R₀ / 2)).exists_bound_of_continuousOn hhcont
  have hhM : ∀ z ∈ closedBall (0 : ComplexModel (m + 1)) (R₀ / 2), |h z| ≤ Mh := fun z hz => by
    simpa [Real.norm_eq_abs] using hMh z hz
  set ρ := R₀ / 4 with hρ
  have hρpos : 0 < ρ := by positivity
  have h2ρ : 2 * ρ = R₀ / 2 := by rw [hρ]; ring
  have hΩ : closedBall (0 : ComplexModel (m + 1)) (2 * ρ) ⊆ UP := by
    rw [h2ρ]; exact fun z hz => (hball (hsub2 hz)).1.1
  obtain ⟨K, -, hK⟩ := hPpsh.exists_nonnegative_compact_upper_bound
    (isCompact_closedBall (0 : ComplexModel (m + 1)) (2 * ρ)) hΩ
  have hballρ : ∀ z ∈ ball (0 : ComplexModel (m + 1)) ρ,
      z ∈ closedBall (0 : ComplexModel (m + 1)) (R₀ / 2) := fun z hz =>
    ball_subset_closedBall (ball_subset_ball (by linarith) hz)
  -- `u' ≤ P + Mh` and `P ≤ u' + Mh` near `0`
  have hupper : ∀ z ∈ closedBall (0 : ComplexModel (m + 1)) (R₀ / 2), u' z ≤ P z + (Mh : EReal) :=
    fun z hz => by
      rw [(hball (hsub2 hz)).1.2]
      exact add_le_add le_rfl (EReal.coe_le_coe_iff.mpr (abs_le.mp (hhM z hz)).2)
  have hlower : ∀ z ∈ closedBall (0 : ComplexModel (m + 1)) (R₀ / 2), P z ≤ u' z + (Mh : EReal) :=
    fun z hz => by
      rw [(hball (hsub2 hz)).1.2]
      have hnn : (0 : ℝ) ≤ h z + Mh := by linarith [(abs_le.mp (hhM z hz)).1]
      calc P z = P z + (0 : EReal) := (add_zero _).symm
        _ ≤ P z + (((h z + Mh : ℝ)) : EReal) := add_le_add le_rfl (EReal.coe_nonneg.mpr hnn)
        _ = P z + (h z : EReal) + (Mh : EReal) := by rw [EReal.coe_add, add_assoc]
  intro γ hγ
  by_cases hγ0 : γ < 0
  · -- a negative exponent: `γ log |z_{m+1}| ≥ 0` near the hyperplane
    refine ⟨ball 0 (min ρ 1), ball_mem_nhds _ (lt_min hρpos one_pos), K + Mh, fun z hz hz0 => ?_⟩
    have hzρ : z ∈ ball (0 : ComplexModel (m + 1)) ρ := ball_subset_ball (min_le_left _ _) hz
    have hlast : ‖z (Fin.last m)‖ < 1 := by
      have h1 := norm_last_le (p := (0 : ComplexModel (m + 1))) (by simp) z
      have h2 : ‖z‖ < min ρ 1 := by simpa using hz
      simp only [sub_zero] at h1
      linarith [min_le_right ρ 1]
    have hlog : Real.log ‖z (Fin.last m)‖ ≤ 0 :=
      Real.log_nonpos (norm_nonneg _) hlast.le
    have hγlog : 0 ≤ γ * Real.log ‖z (Fin.last m)‖ := mul_nonneg_of_nonpos_of_nonpos hγ0.le hlog
    have hPz : P z ≤ (K : EReal) := hK z (by
      rw [h2ρ]; exact hballρ z hzρ)
    calc u' z ≤ P z + (Mh : EReal) := hupper z (hballρ z hzρ)
      _ ≤ (K : EReal) + (Mh : EReal) := add_le_add hPz le_rfl
      _ = ((K + Mh : ℝ) : EReal) := (EReal.coe_add _ _).symm
      _ ≤ ((γ * Real.log ‖z (Fin.last m)‖ + (K + Mh) : ℝ) : EReal) :=
          EReal.coe_le_coe_iff.mpr (by linarith)
  · push Not at hγ0
    set γ₀ : ℝ≥0 := ⟨γ, hγ0⟩ with hγ₀
    -- admissible exponents of `P` along the hyperplane
    have hadm : ∀ q ∈ ball (0 : ComplexModel (m + 1)) ρ, q (Fin.last m) = 0 →
        ∃ γ' > γ, ∃ C : ℝ, ∀ᶠ z in 𝓝[≠] q,
          P z ≤ ((γ' * Real.log ‖z - q‖ + C : ℝ) : EReal) := by
      intro q hq hql
      have hqT : q ∈ Φ.Φ.target := (hball (hsub2 (hballρ q hq))).2.2
      have hqE : Φ.point q ∈ E := Φ.point_mem hqT hql
      have hbot : 0 < lelongNumber (n := m + 1) (fun y => v (π y)) (Φ.point q) →
          v (π (Φ.point q)) = ⊥ :=
        eq_bot_of_lelongNumber_pos (Nat.succ_pos m) hvπ
      have hcomp := LelongNumberComparison.lelongNumber_le_comp
        (u := fun y => v (π y)) (Φ.mdifferentiableAt_point hqT) hbot
      have hlt : (γ₀ : ℝ≥0∞) < lelongNumber (n := m + 1) u' q := by
        refine lt_of_lt_of_le ?_ hcomp
        refine lt_of_lt_of_le ?_ (divisorialLelongNumber_le hqE)
        refine lt_of_le_of_lt ?_ hr
        exact_mod_cast (show γ ≤ (r : ℝ) from hγ.le)
      obtain ⟨γ', hγ', C, hC⟩ := exists_admissible_of_lt_lelongNumber hlt
      refine ⟨γ', hγ', C + Mh, ?_⟩
      have hnear : ∀ᶠ z in 𝓝[≠] q, z ∈ closedBall (0 : ComplexModel (m + 1)) (R₀ / 2) :=
        nhdsWithin_le_nhds (isOpen_ball.mem_nhds (ball_subset_ball (by linarith) hq) |>
          Filter.mem_of_superset <| ball_subset_closedBall)
      filter_upwards [hC, hnear] with z hz hzb
      calc P z ≤ u' z + (Mh : EReal) := hlower z hzb
        _ ≤ ((γ' * Real.log ‖z - q‖ + C : ℝ) : EReal) + (Mh : EReal) := add_le_add hz le_rfl
        _ = ((γ' * Real.log ‖z - q‖ + (C + Mh) : ℝ) : EReal) := by
            rw [← EReal.coe_add]; congr 1; ring
    refine ⟨ball 0 ρ, ball_mem_nhds _ hρpos, K - γ * Real.log ρ + Mh, fun z hz hz0 => ?_⟩
    have hP := le_log_last_add_of_admissible hPpsh (by simp) hΩ hK hadm hz hz0
    calc u' z ≤ P z + (Mh : EReal) := hupper z (hballρ z hz)
      _ ≤ ((γ * Real.log ‖z (Fin.last m)‖ + (K - γ * Real.log ρ) : ℝ) : EReal) + (Mh : EReal) :=
          add_le_add hP le_rfl
      _ = ((γ * Real.log ‖z (Fin.last m)‖ + (K - γ * Real.log ρ + Mh) : ℝ) : EReal) := by
          rw [← EReal.coe_add]; congr 1; ring

/-! ### `π` in flattening coordinates -/

/-- `π` read in the flattening coordinates at `x` and the preferred chart at `π x`. -/
def flatCoordMap (π : Y → Z) {E : Set Y} {x : Y} (Φ : DivisorFlattening (m := m) E x) :
    ComplexModel (m + 1) → ComplexModel (m + 1) :=
  fun z => (complexChartAt (n := m + 1) (π x)).val (π (Φ.point z))

variable (m) in
/-- **The log discrepancy of `E` at `x` is at most `A`** (with respect to `π`): in some flattening
at `x`, the complex Jacobian of `π` is `z_{m+1}^k J'` near `0`, with `J'` holomorphic and not
identically zero on the hyperplane near `0`, and `k + 1 ≤ A`.  With `k = ord_E (J_π)` this is
`A_E ≤ A`, `A_E = 1 + ord_E (J_π)` the log discrepancy (`pc:divisorial-lelong`). -/
def LogDiscrepancyLE (π : Y → Z) (E : Set Y) (x : Y) (A : ℕ) : Prop :=
  ∃ (Φ : DivisorFlattening (m := m) E x) (k : ℕ) (J' : ComplexModel (m + 1) → ℂ), k + 1 ≤ A ∧
    (∀ᶠ z in 𝓝 (0 : ComplexModel (m + 1)), DifferentiableAt ℂ J' z) ∧
    complexJacobian (flatCoordMap π Φ) =ᶠ[𝓝 0] (fun z => z (Fin.last m) ^ k * J' z) ∧
    ∃ᶠ z in 𝓝 (0 : ComplexModel (m + 1)), z (Fin.last m) = 0 ∧ J' z ≠ 0

variable (m) in
/-- `π` is injective off a set `S` whose trace in every preferred chart is Lebesgue-null (a
modification is injective off its exceptional locus, a nowhere dense analytic set). -/
def IsInjectiveOffNull (π : Y → Z) : Prop :=
  ∃ S : Set Y, (∀ y : Y, volume ((complexChartAt (n := m + 1) y).val ''
      (S ∩ (complexChartAt (n := m + 1) y).val.source)) = 0) ∧ InjOn π Sᶜ

namespace DivisorFlattening

variable {E : Set Y} {x : Y} (Φ : DivisorFlattening (m := m) E x)

/-- The domain of `flatCoordMap π Φ`. -/
def flatDomain (π : Y → Z) : Set (ComplexModel (m + 1)) :=
  Φ.Φ.target ∩ {z | π (Φ.point z) ∈ (complexChartAt (n := m + 1) (π x)).val.source}

theorem continuousOn_point : ContinuousOn Φ.point Φ.Φ.target := fun _ hz =>
  (Φ.mdifferentiableAt_point hz).continuousAt.continuousWithinAt

omit [IsComplexManifold (m + 1) Z] in
theorem isOpen_flatDomain {π : Y → Z} (hπ : Continuous π) : IsOpen (Φ.flatDomain π) :=
  ((hπ.comp_continuousOn Φ.continuousOn_point)).isOpen_inter_preimage Φ.Φ.isOpen_target
    (complexChartAt (n := m + 1) (π x)).val.open_source

omit [IsComplexManifold (m + 1) Y] [IsComplexManifold (m + 1) Z] in
theorem zero_mem_flatDomain (π : Y → Z) : (0 : ComplexModel (m + 1)) ∈ Φ.flatDomain π := by
  refine ⟨Φ.zero_mem_target, ?_⟩
  show π (Φ.point 0) ∈ (complexChartAt (n := m + 1) (π x)).val.source
  rw [Φ.point_zero]; exact mem_complexChartAt_source _

omit [IsComplexManifold (m + 1) Y] [IsComplexManifold (m + 1) Z] in
theorem flatCoordMap_zero (π : Y → Z) :
    flatCoordMap π Φ 0 = (complexChartAt (n := m + 1) (π x)).val (π x) := by
  simp only [flatCoordMap, Φ.point_zero]

omit [IsComplexManifold (m + 1) Y] [IsComplexManifold (m + 1) Z] in
theorem chartSymm_flatCoordMap (π : Y → Z) {z : ComplexModel (m + 1)} (hz : z ∈ Φ.flatDomain π) :
    (complexChartAt (n := m + 1) (π x)).val.symm (flatCoordMap π Φ z) = π (Φ.point z) :=
  (complexChartAt (n := m + 1) (π x)).val.left_inv hz.2

theorem differentiableOn_flatCoordMap {π : Y → Z}
    (hπ : ContMDiff 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel (m + 1)) ∞ π) :
    DifferentiableOn ℂ (flatCoordMap π Φ) (Φ.flatDomain π) := by
  intro z hz
  set e := complexChartAt (n := m + 1) x
  set d := complexChartAt (n := m + 1) (π x)
  have hw : Φ.Φ.invFun z ∈ coordinateDomain π e d :=
    ⟨Φ.invFun_mem_target hz.1, hz.2⟩
  have hcd : DifferentiableAt ℂ (coordinateMap π e d) (Φ.Φ.invFun z) :=
    (coordinateMap_contDiffAt hπ e d hw).differentiableAt (by simp)
  have hinv : DifferentiableAt ℂ Φ.Φ.invFun z :=
    Φ.Φ.invFun_holomorphic.differentiableAt (Φ.Φ.isOpen_target.mem_nhds hz.1)
  exact (hcd.comp z hinv).differentiableWithinAt

omit [IsComplexManifold (m + 1) Y] [IsComplexManifold (m + 1) Z] in
/-- **Injectivity off a null set in flattening coordinates.** -/
theorem exists_null_injOn {π : Y → Z} (hinj : IsInjectiveOffNull m π) :
    ∃ N : Set (ComplexModel (m + 1)), volume N = 0 ∧
      InjOn (flatCoordMap π Φ) (Φ.flatDomain π \ N) := by
  obtain ⟨S, hSnull, hSinj⟩ := hinj
  set e := complexChartAt (n := m + 1) x
  set d := complexChartAt (n := m + 1) (π x)
  set T := e.val '' (S ∩ e.val.source) ∩ Φ.Φ.source with hT
  refine ⟨Φ.Φ.toFun '' T, ?_, ?_⟩
  · refine addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume ?_
      (measure_mono_null inter_subset_left (hSnull x))
    exact (Φ.Φ.toFun_holomorphic.mono inter_subset_right).restrictScalars ℝ
  · rintro z ⟨hzD, hzN⟩ z' ⟨hz'D, hz'N⟩ hzz'
    have hnotS : ∀ {w}, w ∈ Φ.flatDomain π → w ∉ Φ.Φ.toFun '' T → Φ.point w ∉ S := by
      intro w hw hwN hwS
      refine hwN ⟨Φ.Φ.invFun w, ⟨⟨Φ.point w, ⟨hwS, Φ.point_mem_source hw.1⟩,
        Φ.chart_point hw.1⟩, Φ.Φ.mapsTo_invFun hw.1⟩, Φ.Φ.right_inv w hw.1⟩
    have hπ : π (Φ.point z) = π (Φ.point z') :=
      d.val.injOn hzD.2 hz'D.2 hzz'
    have hpt : Φ.point z = Φ.point z' := hSinj (hnotS hzD hzN) (hnotS hz'D hz'N) hπ
    rw [← Φ.coord_point hzD.1, ← Φ.coord_point hz'D.1, hpt]

end DivisorFlattening

/-! ### The pointwise estimate -/

/-- On the common zero set of the generators, the generator logarithm is `⊥`. -/
theorem generatorLog_eq_bot_of_normSq_eq_zero' {X : Type*} {k : ℕ} (h : Fin k → X → ℂ) {y : X}
    (hy : generatorNormSq h y = 0) : generatorLog h y = ⊥ := by
  rw [generatorLog_eq_bot_iff]
  intro j
  have hsum : ∀ j' ∈ Finset.univ, (0 : ℝ) ≤ ‖h j' y‖ ^ 2 := fun _ _ => sq_nonneg _
  have := (Finset.sum_eq_zero_iff_of_nonneg hsum).mp hy j (Finset.mem_univ j)
  simpa using this

/-- Off the common zero set, the generator logarithm is the logarithm of the norm square. -/
theorem generatorLog_eq_coe_log' {X : Type*} {k : ℕ} (h : Fin k → X → ℂ) {y : X}
    (hy : generatorNormSq h y ≠ 0) :
    generatorLog h y = (Real.log (generatorNormSq h y) : EReal) := by
  refine generatorLog_of_nonzero ?_
  by_contra hcon
  push Not at hcon
  exact hy (by simp [generatorNormSq, hcon])

/-- The integer `a = ⌈t⌉₊ - 1` used for the vanishing order: `a ≥ t - 1`, and `a < t` unless
`a = 0`. -/
theorem natCeil_sub_one_spec (t : ℝ) :
    (t - 1 ≤ ((⌈t⌉₊ - 1 : ℕ) : ℝ)) ∧ ((⌈t⌉₊ - 1 : ℕ) = 0 ∨ ((⌈t⌉₊ - 1 : ℕ) : ℝ) < t) := by
  rcases Nat.eq_zero_or_pos ⌈t⌉₊ with h0 | hpos
  · have ht : t ≤ 0 := Nat.ceil_eq_zero.mp h0
    rw [h0]
    simp only [zero_tsub, Nat.cast_zero, true_or, and_true]
    linarith
  · have ht : 0 < t := Nat.ceil_pos.mp hpos
    have hcast : ((⌈t⌉₊ - 1 : ℕ) : ℝ) = (⌈t⌉₊ : ℝ) - 1 := by
      rw [Nat.cast_sub hpos]; simp
    refine ⟨?_, Or.inr ?_⟩
    · rw [hcast]; linarith [Nat.le_ceil t]
    · rw [hcast]; linarith [Nat.ceil_lt_add_one ht.le]

/-- **The divisorial estimate at a point** (`pc:demailly-divisorial-lelong`, pointwise).  Let `v`
be `θ`-plurisubharmonic, `φ` of type `(q⁻¹, 𝓘(q v))`, `π` holomorphic and injective off a null
set, and suppose the log discrepancy of `E` at `x` is at most `A`.  For every `r < ν(π^* v, E)`,
`ν(π^* φ, x) ≥ r - 2A/q`. -/
theorem ofReal_sub_le_lelongNumber_comp {π : Y → Z}
    (hπ : ContMDiff 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel (m + 1)) ∞ π)
    (hinj : IsInjectiveOffNull m π)
    {θ : SmoothRealForm (m + 1) Z 2} {v : Z → EReal} (hv : ThetaPlurisubharmonic θ v)
    {φ : Z → EReal} {q : ℕ} (hq : 0 < q)
    (hφ : HasAnalyticSingularitiesOfType (n := m + 1) φ ((q : ℚ)⁻¹)
      (multiplierIdeal (n := m + 1) (q : ℝ) v))
    {E : Set Y} {x : Y} {A : ℕ} (hA : LogDiscrepancyLE m π E x A)
    {r : ℝ≥0} (hr : (r : ℝ≥0∞) < divisorialLelongNumber m (fun y => v (π y)) E) :
    ENNReal.ofReal ((r : ℝ) - 2 * A / q) ≤ lelongNumber (n := m + 1) (fun y => φ (π y)) x := by
  obtain ⟨Φ, k, J', hkA, hJ'd, hJ, hJne⟩ := hA
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  -- the integer `a`
  set t : ℝ := (q : ℝ) * r / 2 - k with ht
  set a : ℕ := ⌈t⌉₊ - 1 with ha
  obtain ⟨hat, ha'⟩ := natCeil_sub_one_spec t
  rw [← ha] at hat ha'
  have hgoal : (r : ℝ) - 2 * A / q ≤ 2 * a / q := by
    have hkA' : ((k : ℝ) + 1) ≤ A := by exact_mod_cast hkA
    have hq0 : (q : ℝ) ≠ 0 := hqR.ne'
    rw [show (r : ℝ) - 2 * A / q = ((q : ℝ) * r - 2 * A) / q by field_simp]
    exact div_le_div_of_nonneg_right (by rw [ht] at hat; linarith) hqR.le
  by_cases ha0 : a = 0
  · -- nothing to prove
    have hle : (r : ℝ) - 2 * A / q ≤ 0 := by simpa [ha0] using hgoal
    rw [ENNReal.ofReal_of_nonpos hle]
    exact zero_le
  have hak : (a : ℝ) + k < (q : ℝ) * r / 2 := by
    rcases ha' with h | h
    · exact absurd h ha0
    · rw [ht] at h; linarith
  -- coordinates
  set e := complexChartAt (n := m + 1) x with he
  set d := complexChartAt (n := m + 1) (π x) with hd
  set F := flatCoordMap π Φ with hF
  set D := Φ.flatDomain π with hD
  have hDo : IsOpen D := Φ.isOpen_flatDomain hπ.continuous
  have h0D : (0 : ComplexModel (m + 1)) ∈ D := Φ.zero_mem_flatDomain π
  have hFd : DifferentiableOn ℂ F D := Φ.differentiableOn_flatCoordMap hπ
  obtain ⟨N, hN, hFinj⟩ := Φ.exists_null_injOn hinj
  -- the generators of `𝓘(q v)` near `π x`
  obtain ⟨-, -, hpres⟩ := hφ
  obtain ⟨U, hUo, hxU, Ng, g, hgd, hgiff, R, CR, hRb, hφeq⟩ := hpres (π x)
  have hgmem : ∀ i, (multiplierIdeal (n := m + 1) (q : ℝ) v).mem (π x) (g i) := fun i =>
    (hgiff (π x) hxU (g i)).mpr (InvertibleIdealQuotient.isInSpanAt_self ⟨i, rfl⟩
      (InvertibleIdealQuotient.holomorphicAt_of_mdifferentiableOn hUo (hgd i) hxU))
  have hgW : ∀ i, ∃ W : Set (ComplexModel (m + 1)), IsOpen W ∧ F 0 ∈ W ∧
      ∫⁻ y in W, multiplierDensity (chartFunction v d) (q : ℝ)
        (fun w => g i (d.val.symm w)) y ≠ ⊤ := fun i => by
    obtain ⟨-, -, W, hWo, hxW, -, -, hfin⟩ := hgmem i
    exact ⟨W, hWo, by rw [hF, Φ.flatCoordMap_zero]; exact hxW, hfin.ne⟩
  have hgF : ∀ i, ∀ᶠ z in 𝓝 (0 : ComplexModel (m + 1)),
      DifferentiableAt ℂ (fun z => g i (d.val.symm (F z))) z := fun i => by
    obtain ⟨-, -, W, hWo, hxW, hgdW, -⟩ := hgmem i
    have hF0W : F 0 ∈ W := by rw [hF, Φ.flatCoordMap_zero]; exact hxW
    have hFc : ContinuousAt F 0 := (hFd.differentiableAt (hDo.mem_nhds h0D)).continuousAt
    filter_upwards [hDo.mem_nhds h0D, hFc.eventually (hWo.mem_nhds hF0W)] with z hzD hzW
    exact (hgdW.differentiableAt (hWo.mem_nhds hzW)).comp z
      (hFd.differentiableAt (hDo.mem_nhds hzD))
  -- the slice bound for `chartFunction v d ∘ F`
  have hslice : ∀ γ < (r : ℝ), ∃ U' ∈ 𝓝 (0 : ComplexModel (m + 1)), ∃ C : ℝ, ∀ z ∈ U',
      z (Fin.last m) ≠ 0 → chartFunction v d (F z) ≤
        ((γ * Real.log ‖z (Fin.last m)‖ + C : ℝ) : EReal) := by
    intro γ hγ
    obtain ⟨U', hU', C, hC⟩ := exists_slice_bound hπ hv Φ hr γ hγ
    refine ⟨U' ∩ D, inter_mem hU' (hDo.mem_nhds h0D), C, fun z hz hz0 => ?_⟩
    have h' := Φ.chartSymm_flatCoordMap π hz.2
    rw [← hd, ← hF] at h'
    show v (d.val.symm (F z)) ≤ _
    rw [h']
    exact hC z hz.1 hz0
  obtain ⟨C, hCbd⟩ := exists_sum_normSq_le_of_lintegral_image (p := 0) (by simp) hDo h0D hFd hN
    hFinj (w := chartFunction v d) (c := q) (ν := r) hqR
    (g := fun i => fun w => g i (d.val.symm w)) hgW hgF hslice hJ'd hJ hJne a (Or.inr hak)
  -- the generators read at the points of `Y`
  have hnear : ∀ᶠ z in 𝓝 (0 : ComplexModel (m + 1)), z ∈ D ∧ π (Φ.point z) ∈ U ∧
      ∑ i, ‖g i (π (Φ.point z))‖ ^ 2 ≤ C * ‖z (Fin.last m)‖ ^ (2 * a) := by
    have hcont : ContinuousAt (fun z => π (Φ.point z)) 0 :=
      hπ.continuous.continuousAt.comp ((Φ.mdifferentiableAt_point Φ.zero_mem_target).continuousAt)
    have hU0 : π (Φ.point 0) ∈ U := by rw [Φ.point_zero]; exact hxU
    filter_upwards [hDo.mem_nhds h0D, hcont.eventually (hUo.mem_nhds hU0), hCbd]
      with z hzD hzU hzC
    refine ⟨hzD, hzU, ?_⟩
    have h' := Φ.chartSymm_flatCoordMap π hzD
    rw [← hd, ← hF] at h'
    simp only [h'] at hzC
    exact hzC
  set c : ℝ := (((q : ℚ)⁻¹ : ℚ) : ℝ) with hc
  have hcq : c = 1 / q := by rw [hc]; push_cast; ring
  have hcpos : 0 < c := by rw [hcq]; positivity
  -- the coordinate Lelong bound
  set φ' : ComplexModel (m + 1) → EReal := fun z => φ (π (Φ.point z)) with hφ'
  set C' : ℝ := max C 1 with hC'
  have hcoord : ∀ᶠ z in 𝓝[≠] (0 : ComplexModel (m + 1)),
      φ' z ≤ ((2 * a / q * Real.log ‖z‖ + (c * Real.log C' + CR) : ℝ) : EReal) := by
    filter_upwards [nhdsWithin_le_nhds hnear, self_mem_nhdsWithin] with z ⟨hzD, hzU, hzC⟩ hz0
    have hz0' : z ≠ 0 := hz0
    have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hz0'
    set y := π (Φ.point z)
    show φ y ≤ _
    rw [hφeq y hzU]
    by_cases hS : generatorNormSq g y = 0
    · rw [generatorLog_eq_bot_of_normSq_eq_zero' g hS,
        EReal.coe_mul_bot_of_pos hcpos, EReal.bot_add]
      exact bot_le
    · rw [generatorLog_eq_coe_log' g hS, ← EReal.coe_mul,
        ← EReal.coe_add, EReal.coe_le_coe_iff]
      have hSpos : 0 < generatorNormSq g y :=
        lt_of_le_of_ne (generatorNormSq_nonneg g y) (Ne.symm hS)
      have hlast : ‖z (Fin.last m)‖ ≤ ‖z‖ := by
        simpa using norm_last_le (p := (0 : ComplexModel (m + 1))) (by simp) z
      have hbd : generatorNormSq g y ≤ C' * ‖z‖ ^ (2 * a) := by
        calc generatorNormSq g y = ∑ i, ‖g i y‖ ^ 2 := rfl
          _ ≤ C * ‖z (Fin.last m)‖ ^ (2 * a) := hzC
          _ ≤ C' * ‖z‖ ^ (2 * a) := by
              have hC0 : 0 ≤ C := by
                by_contra hneg
                push Not at hneg
                have : C * ‖z (Fin.last m)‖ ^ (2 * a) ≤ 0 :=
                  mul_nonpos_of_nonpos_of_nonneg hneg.le (by positivity)
                have hs : (0 : ℝ) < ∑ i, ‖g i y‖ ^ 2 := hSpos
                linarith
              exact mul_le_mul (le_max_left _ _)
                (pow_le_pow_left₀ (norm_nonneg _) hlast _) (by positivity)
                (le_trans hC0 (le_max_left _ _))
      have hlog : Real.log (generatorNormSq g y) ≤ Real.log C' + (2 * a) * Real.log ‖z‖ := by
        have h1 := Real.log_le_log hSpos hbd
        rw [Real.log_mul (by positivity) (by positivity), Real.log_pow] at h1
        push_cast at h1
        linarith
      have hR : R y ≤ CR := (abs_le.mp (hRb y hzU)).2
      calc c * Real.log (generatorNormSq g y) + R y
          ≤ c * (Real.log C' + (2 * a) * Real.log ‖z‖) + CR :=
            add_le_add (mul_le_mul_of_nonneg_left hlog hcpos.le) hR
        _ = 2 * a / q * Real.log ‖z‖ + (c * Real.log C' + CR) := by
            rw [hcq]; ring
  have hcoordL : ENNReal.ofReal (2 * a / q) ≤ lelongNumber (n := m + 1) φ' 0 := by
    refine LelongNumberChartTransport.ofReal_le_lelongNumber (C := c * Real.log C' + CR)
      (by positivity) ?_
    simpa [complexChartAt, chartAt_self_eq] using hcoord
  -- back to `Y`
  have hbot : 0 < lelongNumber (n := m + 1) φ' (Φ.coord x) → φ' (Φ.coord x) = ⊥ := by
    intro _
    rw [Φ.coord_x, hφ']
    show φ (π (Φ.point 0)) = ⊥
    rw [Φ.point_zero, hφeq (π x) hxU]
    have h0 : generatorNormSq g (π x) = 0 := by
      have h := (hnear.self_of_nhds).2.2
      rw [Φ.point_zero] at h
      have ha1 : 2 * a ≠ 0 := by omega
      have hsum : ∑ i, ‖g i (π x)‖ ^ 2 ≤ 0 := by simpa [zero_pow ha1] using h
      exact le_antisymm hsum (Finset.sum_nonneg fun i _ => sq_nonneg _)
    rw [generatorLog_eq_bot_of_normSq_eq_zero' g h0,
      EReal.coe_mul_bot_of_pos hcpos, EReal.bot_add]
  have hcomp := LelongNumberComparison.lelongNumber_le_comp (u := φ') Φ.mdifferentiableAt_coord
    hbot
  rw [Φ.coord_x] at hcomp
  have hcongr : (fun y => φ' (Φ.coord y)) =ᶠ[𝓝 x] fun y => φ (π y) := by
    filter_upwards [Φ.eventually_point_coord] with y hy
    simp only [hφ', hy]
  rw [LelongNumberComparison.lelongNumber_congr hcongr] at hcomp
  exact (ENNReal.ofReal_le_ofReal hgoal).trans (hcoordL.trans hcomp)

/-! ### Along the divisor -/

/-- **Lower bound along `E`** (`pc:demailly-divisorial-lelong`, left inequality):
`ν(π^* v, E) - 2A/q ≤ ν(π^* φ, E)` for `φ` of type `(q⁻¹, 𝓘(q v))`, when the log discrepancy of
`E` is at most `A` at every point of `E`. -/
theorem divisorialLelongNumber_comp_sub_le {π : Y → Z}
    (hπ : ContMDiff 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel (m + 1)) ∞ π)
    (hinj : IsInjectiveOffNull m π)
    {θ : SmoothRealForm (m + 1) Z 2} {v : Z → EReal} (hv : ThetaPlurisubharmonic θ v)
    {φ : Z → EReal} {q : ℕ} (hq : 0 < q)
    (hφ : HasAnalyticSingularitiesOfType (n := m + 1) φ ((q : ℚ)⁻¹)
      (multiplierIdeal (n := m + 1) (q : ℝ) v))
    {E : Set Y} {A : ℕ} (hA : ∀ x ∈ E, LogDiscrepancyLE m π E x A) :
    divisorialLelongNumber m (fun y => v (π y)) E - ENNReal.ofReal (2 * A / q) ≤
      divisorialLelongNumber m (fun y => φ (π y)) E := by
  refine le_iInf₂ fun x hx => ?_
  rw [tsub_le_iff_right]
  refine ENNReal.le_of_forall_nnreal_lt fun r hr => ?_
  have h := ofReal_sub_le_lelongNumber_comp hπ hinj hv hq hφ (hA x hx) hr
  calc (r : ℝ≥0∞) = ENNReal.ofReal (((r : ℝ) - 2 * A / q) + 2 * A / q) := by simp
    _ ≤ ENNReal.ofReal ((r : ℝ) - 2 * A / q) + ENNReal.ofReal (2 * A / q) :=
        ENNReal.ofReal_add_le
    _ ≤ lelongNumber (n := m + 1) (fun y => φ (π y)) x + ENNReal.ofReal (2 * A / q) :=
        add_le_add h le_rfl

omit [IsComplexManifold (m + 1) Y] [TopologicalSpace Z] [ChartedSpace (ComplexModel (m + 1)) Z]
  [IsComplexManifold (m + 1) Z] in
/-- **Upper bound along `E`** (`pc:demailly-divisorial-lelong`, right inequality): if `v ≤ φ`,
then `ν(π^* φ, E) ≤ ν(π^* v, E)`. -/
theorem divisorialLelongNumber_comp_le_of_le (π : Y → Z) {v φ : Z → EReal}
    (hle : ∀ z, v z ≤ φ z) (E : Set Y) :
    divisorialLelongNumber m (fun y => φ (π y)) E ≤
      divisorialLelongNumber m (fun y => v (π y)) E :=
  iInf₂_mono fun _ _ => KahlerCurrentMax.lelongNumber_le_of_eventually_le
    (Eventually.of_forall fun y => hle (π y))

open Hironaka.QuasiEquisingularApproximation Hironaka.PositiveClasses in
/-- **Divisorial Lelong numbers of the terms of a quasi-equisingular approximation with global
type** (`pc:demailly-divisorial-lelong`).  If `(u_k)` is a quasi-equisingular approximation of the
`θ`-psh potential `u` in which `u_k` has type `(2^{-k}, 𝓘(2^k u))` (Demailly's sequence:
`QuasiEquisingularApproximationDemailly.exists_quasiEquisingularApproximation_ofType`), then along
a smooth hypersurface `E` with log discrepancy at most `A` on a modification `π`,
`ν(π^* u, E) - 2A/2^k ≤ ν(π^* u_k, E) ≤ ν(π^* u, E)`. -/
theorem divisorialLelongNumber_quasiEquisingularApproximation {π : Y → Z}
    (hπ : ContMDiff 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel (m + 1)) ∞ π)
    (hinj : IsInjectiveOffNull m π) {omega : KahlerBackground (m + 1) Z}
    {θ : ClosedRealOneOneForm (m + 1) Z} {u : Z → EReal} {ε : ℕ → ℝ} {uSeq : ℕ → Z → EReal}
    (hqea : IsQuasiEquisingularApproximation omega θ u ε uSeq)
    (htype : ∀ k, HasAnalyticSingularitiesOfType (n := m + 1) (uSeq k) (((2 ^ k : ℕ) : ℚ)⁻¹)
      (multiplierIdeal (n := m + 1) ((2 ^ k : ℕ) : ℝ) u))
    {E : Set Y} {A : ℕ} (hA : ∀ x ∈ E, LogDiscrepancyLE m π E x A) (k : ℕ) :
    divisorialLelongNumber m (fun y => u (π y)) E - ENNReal.ofReal (2 * A / ((2 ^ k : ℕ) : ℝ)) ≤
        divisorialLelongNumber m (fun y => uSeq k (π y)) E ∧
      divisorialLelongNumber m (fun y => uSeq k (π y)) E ≤
        divisorialLelongNumber m (fun y => u (π y)) E := by
  refine ⟨divisorialLelongNumber_comp_sub_le hπ hinj hqea.target.1 (by positivity) (htype k) hA,
    divisorialLelongNumber_comp_le_of_le π (fun z => ?_) E⟩
  exact (hqea.term_antitone z).le_of_tendsto (hqea.term_tendsto z) k

end

end Hironaka.DemaillyApproximantDivisorialLelong
