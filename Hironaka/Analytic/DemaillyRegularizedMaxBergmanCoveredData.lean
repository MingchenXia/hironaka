import Hironaka.Analytic.FiniteRegularizedMaxBergmanOffsetFeasibility
import Hironaka.Analytic.FiniteRegularizedMaxOffPoleBergmanBranches
import Hironaka.Analytic.KahlerCurrentRegularizedMaxChartCoordinateWeak
import Hironaka.Analytic.ShiftedBergmanBranchAnyExponent
import Hironaka.Analytic.ShiftedBergmanBranchTop

set_option autoImplicit false

/-!
# The Demailly Bergman data boundary with its smoothness conclusion removed

`Hironaka.DemaillyRegularizedMaxBergmanDataInterface.RegularizedMaxBergmanChartFrameData`
carries, as a field `hsmoothOffPole`, Demailly's Step 3--4 conclusion that the
regularized potential is smooth away from its polar set.  That field is an
*analytic* assumption.  This module removes it.

What replaces it is elementary and combinatorial:

* `hm : 0 < m` — the Bergman level of the atlas is positive, so its branches all
  carry the single coefficient `m⁻¹`;
* `hqcount : atlas.count ≤ q` — the recursion is run to the end;
* `hcover` — the *cores* `inner i`, on which the raw comparisons were already
  assumed, cover `M`.

`RegularizedMaxBergmanCoveredChartFrameData.smoothOffPole` then *proves* the
removed field, through
`Hironaka.FiniteRegularizedMaxOffPoleBergmanBranches.regularizedMaxStageKahlerCurrent_hasManifoldAnalyticSingularitiesSmoothOffPole_shiftedBergman`,
in the `I-0489` convention (bounded remainder, smooth off the poles).  No
statement of the existing interface changes; the interface's own external input
is discharged from the one below in
`Hironaka.DemaillyRegularizedMaxBergmanDataInterface`.

The three added fields are not free: `hcover` is tied to the same shrink
`inner` for which `h_lower` and `h_unshifted_upper` were assumed, and `h_lower`
cannot hold for an arbitrary shrink (near `∂(atlas.patch i).patch.source` the
Bergman branch decreases without bound, so the core inequality fails there).
What is gained is that a deep regularity conclusion has become a covering
condition on the patches Demailly's construction already produces.

The superseded existence record `demailly1992_nonempty_regularizedMaxBergmanCoveredChartFrameData`
(a `sorry`; Demailly 1992, Theorem 1.1 and Proposition 3.7, in this data form) was retired on
2 Oct 2026 (human decision I-0902 item 2, TN.4 record #7): it had left the main theorem's cone in
run 0091 and its consumer chain was deleted first (19ddd720 and the transport in
`Hironaka.DemaillyRegularizedMaxBergmanDataInterface`).  Demailly 1992 enters the project once,
as `Hironaka.Demailly1992AlgebraicApproximation`.  The structure and its proved projections stay.
-/

open Set Filter
open scoped BigOperators Manifold Topology

namespace Hironaka.DemaillyRegularizedMaxBergmanCoveredData

open Hironaka
open Hironaka
open Hironaka.AnalyticGluingData
open Hironaka.GlobalAnalyticSingularities
open Hironaka.HolomorphicIdealSheaves
open Hironaka
open Hironaka.NumericalRestrictedVolumeScaffold
open Hironaka.ChartCoordinateHolomorphicFrameDescent
open Hironaka.ChartGeneratorLift
open Hironaka.FiniteRegularizedMaxBergmanOffsetFeasibility
open Hironaka.FiniteRegularizedMaxCollarGluing
open Hironaka.FiniteRegularizedMaxCoreCover
open Hironaka.FiniteRegularizedMaxOffPoleBergmanBranches
open Hironaka.KahlerCurrentRegularizedMaxChartCoordinateWeak
open Hironaka.KahlerCurrentRegularizationRegularizedMax
open Hironaka.QuasiEquisingularBergmanAtlas
open Hironaka.QuasiEquisingularBergmanBranch
open Hironaka.ShiftedBergmanBranch
open Hironaka.ShiftedBergmanBranchAnyExponent
open Hironaka.ShiftedBergmanBranchTop

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- Finite regularized-max Bergman data with a **covered core** in place of a
smoothness conclusion.

Every field except `hm`, `hqcount` and `hcover` is byte-identical to the
corresponding field of
`Hironaka.DemaillyRegularizedMaxBergmanDataInterface.RegularizedMaxBergmanChartFrameData`,
whose field `hsmoothOffPole` is absent here and proved below instead. -/
structure RegularizedMaxBergmanCoveredChartFrameData
    {alpha : RealBottChern n M} (T : KahlerCurrent alpha) where
  m : ℕ
  hm : 0 < m
  atlas : FiniteUniformLocalBergmanAtlas
    (T.representative - T.lowerBound.form).val T.potential m
  δ : ℝ
  hδ : 0 < δ
  inner : Fin atlas.count → Set M
  hinner_open : ∀ i, IsOpen (inner i)
  hclosure : ∀ i, closure (inner i) ⊆ (atlas.patch i).patch.source
  Cminus : Fin atlas.count → ℝ
  Cplus : Fin atlas.count → ℝ
  hfeasible : ∀ i, Cminus i + Cplus i + 2 * δ ≤ 0
  h_lower : ∀ i, ∀ x ∈ inner i,
    finiteRegularizedMaxGlued δ
        (fun j => ((atlas.patch j).patch.source : Set M))
        (fun j => shiftedBergmanBranch (atlas.patch j).patch (Cminus j + δ))
        T.potential i.val x ≤
      bergmanBranch (atlas.patch i).patch x + (Cminus i : EReal)
  h_unshifted_upper : ∀ i, ∀ x ∈ ((atlas.patch i).patch.source : Set M) \ inner i,
    bergmanBranch (atlas.patch i).patch x ≤
      finiteRegularizedMaxGlued δ
        (fun j => ((atlas.patch j).patch.source : Set M))
        (fun j => shiftedBergmanBranch (atlas.patch j).patch (Cminus j + δ))
        T.potential i.val x + (Cplus i : EReal)
  /-- **The cores cover `M`.**  This is what replaces the analytic smoothness
  field: the same shrink `inner` on which the raw comparisons above were
  assumed is a cover. -/
  hcover : ∀ x : M, ∃ i, x ∈ (regularizedMaxCoreData_of_feasible_sum_unshifted_comparisons
    atlas δ T.potential inner hinner_open hclosure Cminus Cplus hfeasible h_lower
      h_unshifted_upper).core.inner i
  q : ℕ
  /-- The recursion is run through every patch of the atlas. -/
  hqcount : atlas.count ≤ q
  c : ℚ
  hc : 0 < c
  chart : M → ComplexChart n M
  coordinateDomain : M → Set (ComplexModel n)
  hcoordinateDomain_open : ∀ x, IsOpen (coordinateDomain x)
  hcoordinateDomain_target : ∀ x, coordinateDomain x ⊆ (chart x).val.target
  hchartcover : ∀ x, x ∈ domain (chart x) (coordinateDomain x)
  N : M → ℕ
  F : ∀ x, Fin (N x) → ComplexModel n → ℂ
  hFanalytic : ∀ x i, AnalyticOnNhd ℂ (F x i) (coordinateDomain x)
  R : M → M → ℝ
  hRbound : ∀ x, ∃ C : ℝ, ∀ y ∈ domain (chart x) (coordinateDomain x), |R x y| ≤ C
  hformula : ∀ x y, y ∈ domain (chart x) (coordinateDomain x) →
    (regularizedMaxStageKahlerCurrent T hδ
      (regularizedMaxCoreData_of_feasible_sum_unshifted_comparisons
        atlas δ T.potential inner hinner_open hclosure Cminus Cplus hfeasible h_lower
          h_unshifted_upper).core.toRegularizedMaxCollarData
      (fun i => shiftedBergmanBranch_thetaPlurisubharmonicOn_of_anyExponent
        (atlas.patch i).patch (Cminus i + δ)) q).potential y =
        ((c : ℝ) : EReal) * generatorLog (F x) ((chart x).val y) + (R x y : EReal)
  Aframe : ∀ x y, Fin (N y) → Fin (N x) → M → ℂ
  Bframe : ∀ x y, Fin (N x) → Fin (N y) → M → ℂ
  hAhol : ∀ x y, y ∈ domain (chart x) (coordinateDomain x) → ∀ j i,
    HolomorphicAt n (Aframe x y j i) y
  hBhol : ∀ x y, y ∈ domain (chart x) (coordinateDomain x) → ∀ i j,
    HolomorphicAt n (Bframe x y i j) y
  hforward : ∀ x y, y ∈ domain (chart x) (coordinateDomain x) → ∀ j,
    generator (chart y) (F y) j =ᶠ[𝓝 y] fun z =>
      ∑ i, Aframe x y j i z * generator (chart x) (F x) i z
  hbackward : ∀ x y, y ∈ domain (chart x) (coordinateDomain x) → ∀ i,
    generator (chart x) (F x) i =ᶠ[𝓝 y] fun z =>
      ∑ j, Bframe x y i j z * generator (chart y) (F y) j z

namespace RegularizedMaxBergmanCoveredChartFrameData

variable {alpha : RealBottChern n M} {T : KahlerCurrent alpha}

/-- The `θ`-PSH-ness of the shifted branches used throughout. -/
theorem branch_thetaPlurisubharmonicOn (D : RegularizedMaxBergmanCoveredChartFrameData T) (i) :
    ThetaPlurisubharmonicOn (T.representative - T.lowerBound.form).val
      (shiftedBergmanBranch (D.atlas.patch i).patch (D.Cminus i + D.δ))
      ((D.atlas.patch i).patch.source : Set M) :=
  shiftedBergmanBranch_thetaPlurisubharmonicOn_of_anyExponent
    (D.atlas.patch i).patch (D.Cminus i + D.δ)

/-- **Demailly's Step 3--4 smoothness conclusion, proved from the cover.**

This is exactly the field `hsmoothOffPole` of
`Hironaka.DemaillyRegularizedMaxBergmanDataInterface.RegularizedMaxBergmanChartFrameData`,
for the data assembled from `D`. -/
theorem smoothOffPole (D : RegularizedMaxBergmanCoveredChartFrameData T) :
    HasManifoldAnalyticSingularitiesSmoothOffPole (n := n)
      (regularizedMaxStageKahlerCurrent T D.hδ
        (regularizedMaxCoreData_of_feasible_sum_unshifted_comparisons
          D.atlas D.δ T.potential D.inner D.hinner_open D.hclosure D.Cminus D.Cplus D.hfeasible
            D.h_lower D.h_unshifted_upper).core.toRegularizedMaxCollarData
        (fun i => shiftedBergmanBranch_thetaPlurisubharmonicOn_of_anyExponent
          (D.atlas.patch i).patch (D.Cminus i + D.δ)) D.q).potential :=
  regularizedMaxStageKahlerCurrent_hasManifoldAnalyticSingularitiesSmoothOffPole_shiftedBergman
    T D.hm D.atlas D.hδ (fun i => D.Cminus i + D.δ)
    (regularizedMaxCoreData_of_feasible_sum_unshifted_comparisons
      D.atlas D.δ T.potential D.inner D.hinner_open D.hclosure D.Cminus D.Cplus D.hfeasible
        D.h_lower D.h_unshifted_upper).core
    (fun i => D.branch_thetaPlurisubharmonicOn i) D.hcover D.hqcount

/-- The regularization endpoint, from covered data alone.  Identical in
statement to
`Hironaka.DemaillyRegularizedMaxBergmanDataInterface.RegularizedMaxBergmanChartFrameData.exists_kahlerCurrent_poleSet_subset_lelongNumber_pos`. -/
theorem exists_kahlerCurrent_poleSet_subset_lelongNumber_pos
    (D : RegularizedMaxBergmanCoveredChartFrameData T) :
    ∃ S : KahlerCurrent alpha,
      HasAnalyticSingularities (n := n) S.potential ∧
        HasManifoldAnalyticSingularitiesSmoothOffPole (n := n) S.potential ∧
        poleSet S.potential ⊆ {x | 0 < lelongNumber (n := n) T.potential x} := by
  have hbranchtop : ∀ i x,
      shiftedBergmanBranch (D.atlas.patch i).patch (D.Cminus i + D.δ) x ≠ ⊤ :=
    fun i => shiftedBergmanBranch_ne_top_of_thetaPlurisubharmonicOn
      (D.atlas.patch i).patch (D.Cminus i + D.δ) (D.branch_thetaPlurisubharmonicOn i)
  exact
    exists_kahlerCurrent_poleSet_subset_lelongNumber_pos_of_regularizedMaxStage_of_chartCoordinateMutualHolomorphicGeneratorExpansions_smoothOffPole
      T D.hδ
      (regularizedMaxCoreData_of_feasible_sum_unshifted_comparisons
        D.atlas D.δ T.potential D.inner D.hinner_open D.hclosure D.Cminus D.Cplus D.hfeasible
          D.h_lower D.h_unshifted_upper).core
      (fun i => D.branch_thetaPlurisubharmonicOn i) hbranchtop D.q D.c D.hc D.chart
      D.coordinateDomain D.hcoordinateDomain_open D.hcoordinateDomain_target D.hchartcover
      D.N D.F D.hFanalytic D.R D.hRbound D.hformula D.Aframe D.Bframe D.hAhol D.hBhol
      D.hforward D.hbackward D.smoothOffPole

end RegularizedMaxBergmanCoveredChartFrameData

end

end Hironaka.DemaillyRegularizedMaxBergmanCoveredData
