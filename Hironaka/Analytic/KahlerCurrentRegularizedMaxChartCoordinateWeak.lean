import Hironaka.Analytic.KahlerCurrentRegularizationRegularizedMax
import Hironaka.Analytic.ChartCoordinateHolomorphicFrameDescent

/-!
# Regularized-max Kähler-current endpoint with smoothness only off its poles

The coordinate finite-generator formulas below prove global analytic
singularities with a bounded remainder.  They do not make that remainder smooth
across the zero set of the generators.  Demailly's Step 3--4 regularization
does additionally give smoothness on the complement of that polar set; that
separate conclusion is therefore an explicit hypothesis of this bridge.

The Kähler-current construction and its Lelong comparison are proved from the
regularized-max stage.  No smooth-across-poles conclusion is used or produced.
-/

set_option autoImplicit false

open Set Filter
open scoped BigOperators Manifold Topology

namespace Hironaka.KahlerCurrentRegularizedMaxChartCoordinateWeak

open Hironaka
open Hironaka
open Hironaka.AnalyticGluingData
open Hironaka.GlobalAnalyticSingularities
open Hironaka.HolomorphicIdealSheaves
open Hironaka
open Hironaka.NumericalRestrictedVolumeScaffold
open Hironaka.ChartCoordinateHolomorphicFrameDescent
open Hironaka.ChartGeneratorLift
open Hironaka.FiniteRegularizedMaxCollarGluing
open Hironaka.FiniteRegularizedMaxCoreCover
open Hironaka.KahlerCurrentRegularizationRegularizedMax

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- The displayed coordinate formulas prove the bounded-remainder analytic
singularity convention.  Smoothness away from the polar set is a distinct
Step 3--4 conclusion supplied as `hsmoothOffPole`; the stage itself gives the
Kähler-current and Lelong-number assertions. -/
theorem exists_kahlerCurrent_poleSet_subset_lelongNumber_pos_of_regularizedMaxStage_of_chartCoordinateMutualHolomorphicGeneratorExpansions_smoothOffPole
    {alpha : RealBottChern n M} (T : KahlerCurrent alpha) {δ : ℝ} (hδ : 0 < δ)
    {q : ℕ} {U : Fin q → Set M} {branch : Fin q → M → EReal}
    (H : RegularizedMaxCoreData δ U branch T.potential)
    (hbranch : ∀ i, ThetaPlurisubharmonicOn
      (T.representative - T.lowerBound.form).val (branch i) (U i))
    (hbranchtop : ∀ i x, branch i x ≠ ⊤)
    (k : ℕ)
    (c : ℚ) (hc : 0 < c)
    (e : M → ComplexChart n M) (W : M → Set (ComplexModel n))
    (hWopen : ∀ x, IsOpen (W x))
    (hWtarget : ∀ x, W x ⊆ (e x).val.target)
    (hchartcover : ∀ x, x ∈ domain (e x) (W x))
    (N : M → ℕ) (F : ∀ x, Fin (N x) → ComplexModel n → ℂ)
    (hFanalytic : ∀ x i, AnalyticOnNhd ℂ (F x i) (W x))
    (R : M → M → ℝ)
    (hRbound : ∀ x, ∃ C : ℝ, ∀ y ∈ domain (e x) (W x), |R x y| ≤ C)
    (hformula : ∀ x y, y ∈ domain (e x) (W x) →
      (regularizedMaxStageKahlerCurrent T hδ H.toRegularizedMaxCollarData hbranch k).potential y =
        ((c : ℝ) : EReal) * generatorLog (F x) ((e x).val y) + (R x y : EReal))
    (A : ∀ x y, Fin (N y) → Fin (N x) → M → ℂ)
    (B : ∀ x y, Fin (N x) → Fin (N y) → M → ℂ)
    (hAhol : ∀ x y, y ∈ domain (e x) (W x) → ∀ j i, HolomorphicAt n (A x y j i) y)
    (hBhol : ∀ x y, y ∈ domain (e x) (W x) → ∀ i j, HolomorphicAt n (B x y i j) y)
    (hforward : ∀ x y, y ∈ domain (e x) (W x) → ∀ j,
      generator (e y) (F y) j =ᶠ[𝓝 y] fun z =>
        ∑ i, A x y j i z * generator (e x) (F x) i z)
    (hbackward : ∀ x y, y ∈ domain (e x) (W x) → ∀ i,
      generator (e x) (F x) i =ᶠ[𝓝 y] fun z =>
        ∑ j, B x y i j z * generator (e y) (F y) j z)
    (hsmoothOffPole : HasManifoldAnalyticSingularitiesSmoothOffPole (n := n)
      (regularizedMaxStageKahlerCurrent T hδ H.toRegularizedMaxCollarData hbranch k).potential) :
    ∃ S : KahlerCurrent alpha,
      HasAnalyticSingularities (n := n) S.potential ∧
        HasManifoldAnalyticSingularitiesSmoothOffPole (n := n) S.potential ∧
        poleSet S.potential ⊆ {x | 0 < lelongNumber (n := n) T.potential x} := by
  let S := regularizedMaxStageKahlerCurrent T hδ H.toRegularizedMaxCollarData hbranch k
  have hanalytic : HasAnalyticSingularities (n := n) S.potential := by
    exact hasAnalyticSingularities_of_chartCoordinateMutualHolomorphicGeneratorExpansions
      (n := n) (M := M) c hc e W hWopen hWtarget hchartcover N F hFanalytic R hRbound
        (by simpa only [S] using hformula) A B hAhol hBhol hforward hbackward
  refine ⟨S, hanalytic, ?_, ?_⟩
  · simpa only [S] using hsmoothOffPole
  · intro x hx
    exact (AnalyticSingularityPoleLelong.lelongNumber_pos_of_hasAnalyticSingularities
      hanalytic hx).trans_le
        (lelongNumber_regularizedMaxStageKahlerCurrent_le T hδ H.toRegularizedMaxCollarData
          hbranch hbranchtop k x)

end

end Hironaka.KahlerCurrentRegularizedMaxChartCoordinateWeak
