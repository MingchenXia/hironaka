import Hironaka.Analytic.DemaillyRegularizedMaxBergmanCoveredData
import Hironaka.Analytic.FiniteRegularizedMaxBergmanOffsetFeasibility
import Hironaka.Analytic.KahlerCurrentRegularizedMaxChartCoordinateWeak
import Hironaka.Analytic.ShiftedBergmanBranchAnyExponent
import Hironaka.Analytic.ShiftedBergmanBranchTop

set_option autoImplicit false

/-!
# The precise finite Bergman data boundary in Demailly regularization

The remaining input from Demailly's regularization is recorded here as the
existence of finite Bergman chart-frame data.  The structure is deliberately a
data interface, rather than a second version of the desired Kähler-current
conclusion: its fields are exactly the hypotheses consumed by the proved weak
regularized-max bridge.  In particular, it asks for the raw collar estimates,
coordinate formulas, and mutually spanning holomorphic transition frames.  No
claim is made that an arbitrary atlas automatically carries such data.

The remaining analytic construction — Demailly's weighted Bergman
approximation, its local estimates and finite coordinate presentations, and the
compatible overlap frames needed by global coherent ideal descent — is no
longer stated here.  It had moved to
`Hironaka.DemaillyRegularizedMaxBergmanCoveredData`, in a form that does **not**
assume smoothness away from the polar set: there that conclusion is proved from
the cores covering `M`.

The existence statement `demailly1992_nonempty_regularizedMaxBergmanChartFrameData`
that transported that input was retired on 2 Oct 2026 (human decision I-0902
item 2, TN.4 record #7): the main theorem's Demailly route goes through
`Hironaka.Demailly1992AlgebraicApproximation` instead, and its only consumer
(`KahlerCurrentRegularization.demailly1992_exists_kahlerCurrent_poleSet_subset_lelongNumber_pos`)
was deleted first (19ddd720).  The structure and the proved bridge stay.
-/

open Set Filter
open scoped BigOperators Manifold Topology

namespace Hironaka.DemaillyRegularizedMaxBergmanDataInterface

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

/-- The finite regularized-max Bergman data whose construction is the remaining
analytic content of Demailly regularization.  Every field is an actual premise
of the weak regularized-max bridge; the final bridge is proved below by
projection from this structure. -/
structure RegularizedMaxBergmanChartFrameData
    {alpha : RealBottChern n M} (T : KahlerCurrent alpha) where
  m : ℕ
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
  q : ℕ
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
  /-- This is Demailly's Step 3--4 smoothness conclusion for the regularized
  potential on the complement of its polar set.  It is deliberately separate
  from `hformula`: the latter has only a bounded remainder and cannot establish
  smoothness at a pole. -/
  hsmoothOffPole : HasManifoldAnalyticSingularitiesSmoothOffPole (n := n)
    (regularizedMaxStageKahlerCurrent T hδ
      (regularizedMaxCoreData_of_feasible_sum_unshifted_comparisons
        atlas δ T.potential inner hinner_open hclosure Cminus Cplus hfeasible h_lower
          h_unshifted_upper).core.toRegularizedMaxCollarData
      (fun i => shiftedBergmanBranch_thetaPlurisubharmonicOn_of_anyExponent
        (atlas.patch i).patch (Cminus i + δ)) q).potential

/-- The proved finite Bergman bridge consumes the fields of a Demailly data
package and produces the original regularization conclusion without an
additional source assumption. -/
theorem RegularizedMaxBergmanChartFrameData.exists_kahlerCurrent_poleSet_subset_lelongNumber_pos
    {alpha : RealBottChern n M} (T : KahlerCurrent alpha)
    (D : RegularizedMaxBergmanChartFrameData T) :
    ∃ S : KahlerCurrent alpha,
      HasAnalyticSingularities (n := n) S.potential ∧
        HasManifoldAnalyticSingularitiesSmoothOffPole (n := n) S.potential ∧
        poleSet S.potential ⊆ {x | 0 < lelongNumber (n := n) T.potential x} := by
  let H := (regularizedMaxCoreData_of_feasible_sum_unshifted_comparisons
    D.atlas D.δ T.potential D.inner D.hinner_open D.hclosure D.Cminus D.Cplus D.hfeasible
      D.h_lower D.h_unshifted_upper).core
  have hbranch : ∀ i, ThetaPlurisubharmonicOn
      (T.representative - T.lowerBound.form).val
      (shiftedBergmanBranch (D.atlas.patch i).patch (D.Cminus i + D.δ))
      ((D.atlas.patch i).patch.source : Set M) :=
    fun i => shiftedBergmanBranch_thetaPlurisubharmonicOn_of_anyExponent
      (D.atlas.patch i).patch (D.Cminus i + D.δ)
  have hbranchtop : ∀ i x,
      shiftedBergmanBranch (D.atlas.patch i).patch (D.Cminus i + D.δ) x ≠ ⊤ :=
    fun i => shiftedBergmanBranch_ne_top_of_thetaPlurisubharmonicOn
      (D.atlas.patch i).patch (D.Cminus i + D.δ) (hbranch i)
  exact
    exists_kahlerCurrent_poleSet_subset_lelongNumber_pos_of_regularizedMaxStage_of_chartCoordinateMutualHolomorphicGeneratorExpansions_smoothOffPole
      T D.hδ H hbranch hbranchtop D.q D.c D.hc D.chart D.coordinateDomain D.hcoordinateDomain_open
      D.hcoordinateDomain_target D.hchartcover D.N D.F D.hFanalytic D.R D.hRbound D.hformula
      D.Aframe D.Bframe D.hAhol D.hBhol D.hforward D.hbackward D.hsmoothOffPole

end

end Hironaka.DemaillyRegularizedMaxBergmanDataInterface
