import Hironaka.Analytic.FiniteRegularizedMaxCoreCover
import Hironaka.Analytic.AnalyticSingularityPoleLelong
import Hironaka.Analytic.GlobalAnalyticSingularities
import Hironaka.Coherence.FiniteGeneratorIdealDescent

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The Kähler-current endpoint of the regularized-max finite stage

This is the counterpart of
`Hironaka.KahlerCurrentRegularizationFiniteBergman.exists_kahlerCurrent_poleSet_subset_lelongNumber_pos_of_finiteShiftedBergman`
built on the regularized-max recursion instead of the shifted one.  The
shifted assembly needs `ShiftedLaterCoreSeparation` together with a core cover,
and on a connected manifold those two force a single patch, so it cannot be
applied to the multi-chart atlas Demailly regularization produces (I-0304).
The assembly below needs the core cover but NOT the separation.

Nothing is asked of the seed, i.e. of the potential of the arbitrary Kähler
current `T` being regularized: the core cover erases it
(`FiniteRegularizedMaxCoreCover`), exactly as in the shifted recursion.  The
alignment hypothesis `PolewiseAlignedBranches` relates only the branches to each
other, which is the situation on overlapping Bergman charts.

What remains open is stated honestly and is what it was before, minus the
separation:

* `PolewiseAlignedBranches` — at each chart point one coefficient and one
  generator family presents every branch that is a pole there;
* `hcoherent` — the local presentations come from one global ideal
  (`HasAnalyticSingularities`).

The Lelong comparison is no longer an input: every regularized-max stage is
pointwise at least its seed, and the project proves the induced Lelong-number
inequality below.

No new interface is introduced: every hypothesis is a property of the explicitly
constructed glue, not an abstract existence assumption.
-/

open Set Filter
open scoped Topology Manifold

namespace Hironaka.KahlerCurrentRegularizationRegularizedMax

open Hironaka
open Hironaka
open Hironaka.AnalyticGluingData
open Hironaka.GlobalAnalyticSingularities
open Hironaka.HolomorphicIdealSheaves
open Hironaka
open Hironaka.NumericalRestrictedVolumeScaffold
open Hironaka.FiniteRegularizedMaxCollarGluing
open Hironaka.FiniteRegularizedMaxCoreCover
open Hironaka.FiniteGeneratorIdealDescent

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- The finite regularized-max stage, formed with the strict background of `T`,
is a Kähler current in the SAME Bott--Chern class with the same lower bound. -/
def regularizedMaxStageKahlerCurrent {alpha : RealBottChern n M} (T : KahlerCurrent alpha)
    {δ : ℝ} (hδ : 0 < δ) {q : ℕ} {U : Fin q → Set M} {branch : Fin q → M → EReal}
    (H : RegularizedMaxCollarData δ U branch T.potential)
    (hbranch : ∀ i, ThetaPlurisubharmonicOn
      (T.representative - T.lowerBound.form).val (branch i) (U i))
    (k : ℕ) : KahlerCurrent alpha where
  representative := T.representative
  represents := T.represents
  potential := finiteRegularizedMaxGlued δ U branch T.potential k
  lowerBound := T.lowerBound
  strictlyPsh :=
    isThetaPshPotential_finiteRegularizedMaxGlued hδ H hbranch T.strictlyPsh k

/-- **The regularized-max stage realises the strong CT22 convention**, with no
separation hypothesis and nothing assumed about the seed `T.potential`. -/
theorem regularizedMaxStageKahlerCurrent_hasManifoldSmoothAnalyticSingularities
    {alpha : RealBottChern n M} (T : KahlerCurrent alpha) {δ : ℝ} (hδ : 0 < δ)
    {q : ℕ} {U : Fin q → Set M} {branch : Fin q → M → EReal}
    (H : RegularizedMaxCoreData δ U branch T.potential)
    (hbranch : ∀ i, ThetaPlurisubharmonicOn
      (T.representative - T.lowerBound.form).val (branch i) (U i))
    (hbranchtop : ∀ i x, branch i x ≠ ⊤)
    (hbranchsing : ∀ (i : Fin q) (e : ComplexChart n M) (z : ComplexModel n),
      z ∈ e.val.target → e.val.symm z ∈ U i →
        HasSmoothAnalyticSingularitiesAt (chartFunction (branch i) e) z)
    (halign : PolewiseAlignedBranches (n := n) U branch)
    (hcover : ∀ x : M, ∃ i : Fin q, x ∈ H.inner i) {k : ℕ} (hk : q ≤ k) :
    HasManifoldSmoothAnalyticSingularities (n := n)
      (regularizedMaxStageKahlerCurrent T hδ H.toRegularizedMaxCollarData hbranch k).potential :=
  hasManifoldSmoothAnalyticSingularities_finiteRegularizedMaxGlued_of_coreCover hδ H
    hbranchtop (Hironaka.RegularizedMaxERealPshRoute.ThetaPlurisubharmonic.ne_top
      T.strictlyPsh.1) hbranchsing halign hcover hk

/-- The regularized-max stage is pointwise no smaller than its seed, so its
Lelong number is pointwise no larger.  This removes the Lelong comparison
from the global Bergman input: it is a formal consequence of the finite
recursion, rather than an additional Demailly regularization hypothesis. -/
theorem lelongNumber_regularizedMaxStageKahlerCurrent_le
    {alpha : RealBottChern n M} (T : KahlerCurrent alpha) {δ : ℝ} (hδ : 0 < δ)
    {q : ℕ} {U : Fin q → Set M} {branch : Fin q → M → EReal}
    (H : RegularizedMaxCollarData δ U branch T.potential)
    (hbranch : ∀ i, ThetaPlurisubharmonicOn
      (T.representative - T.lowerBound.form).val (branch i) (U i))
    (hbranchtop : ∀ i x, branch i x ≠ ⊤) (k : ℕ) (x : M) :
    lelongNumber (n := n)
        (regularizedMaxStageKahlerCurrent T hδ H hbranch k).potential x ≤
      lelongNumber (n := n) T.potential x := by
  apply KahlerCurrentMax.lelongNumber_le_of_eventually_le
  exact Filter.Eventually.of_forall fun y =>
    seed_le_finiteRegularizedMaxGlued hδ hbranchtop
      (Hironaka.RegularizedMaxERealPshRoute.ThetaPlurisubharmonic.ne_top T.strictlyPsh.1)
      k y

/-- **The final assembly.**  Compare the shifted-collar version: the hypothesis
`ShiftedLaterCoreSeparation` is gone, and with it the connectedness obstruction;
the core cover, which the shifted version also needs, stays.  The remaining
global Demailly claim is coherence of the local presentations into one global
analytic ideal. -/
theorem exists_kahlerCurrent_poleSet_subset_lelongNumber_pos_of_regularizedMaxStage
    {alpha : RealBottChern n M} (T : KahlerCurrent alpha) {δ : ℝ} (hδ : 0 < δ)
    {q : ℕ} {U : Fin q → Set M} {branch : Fin q → M → EReal}
    (H : RegularizedMaxCoreData δ U branch T.potential)
    (hbranch : ∀ i, ThetaPlurisubharmonicOn
      (T.representative - T.lowerBound.form).val (branch i) (U i))
    (hbranchtop : ∀ i x, branch i x ≠ ⊤)
    (hbranchsing : ∀ (i : Fin q) (e : ComplexChart n M) (z : ComplexModel n),
      z ∈ e.val.target → e.val.symm z ∈ U i →
        HasSmoothAnalyticSingularitiesAt (chartFunction (branch i) e) z)
    (halign : PolewiseAlignedBranches (n := n) U branch)
    (hcover : ∀ x : M, ∃ i : Fin q, x ∈ H.inner i) {k : ℕ} (hk : q ≤ k)
    (hcoherent : HasAnalyticSingularities (n := n)
      (regularizedMaxStageKahlerCurrent T hδ H.toRegularizedMaxCollarData hbranch k).potential) :
    ∃ S : KahlerCurrent alpha,
      HasAnalyticSingularities (n := n) S.potential ∧
        HasManifoldSmoothAnalyticSingularities (n := n) S.potential ∧
        poleSet S.potential ⊆ {x | 0 < lelongNumber (n := n) T.potential x} := by
  refine ⟨regularizedMaxStageKahlerCurrent T hδ H.toRegularizedMaxCollarData hbranch k,
    hcoherent,
    regularizedMaxStageKahlerCurrent_hasManifoldSmoothAnalyticSingularities T hδ H hbranch
      hbranchtop hbranchsing halign hcover hk, ?_⟩
  intro x hx
  exact (AnalyticSingularityPoleLelong.lelongNumber_pos_of_hasAnalyticSingularities
    hcoherent hx).trans_le
      (lelongNumber_regularizedMaxStageKahlerCurrent_le T hδ H.toRegularizedMaxCollarData
        hbranch hbranchtop k x)

/-- The regularized-max endpoint can consume an explicit local generator
descent package in place of a bare global-coherence assertion.  Thus the only
global analytic input is stated as the actual span compatibility of the local
finite families, together with their bounded-remainder formulas. -/
theorem exists_kahlerCurrent_poleSet_subset_lelongNumber_pos_of_regularizedMaxStage_of_localGeneratorDescent
    {alpha : RealBottChern n M} (T : KahlerCurrent alpha) {δ : ℝ} (hδ : 0 < δ)
    {q : ℕ} {U : Fin q → Set M} {branch : Fin q → M → EReal}
    (H : RegularizedMaxCoreData δ U branch T.potential)
    (hbranch : ∀ i, ThetaPlurisubharmonicOn
      (T.representative - T.lowerBound.form).val (branch i) (U i))
    (hbranchtop : ∀ i x, branch i x ≠ ⊤)
    (hbranchsing : ∀ (i : Fin q) (e : ComplexChart n M) (z : ComplexModel n),
      z ∈ e.val.target → e.val.symm z ∈ U i →
        HasSmoothAnalyticSingularitiesAt (chartFunction (branch i) e) z)
    (halign : PolewiseAlignedBranches (n := n) U branch)
    (hcover : ∀ x : M, ∃ i : Fin q, x ∈ H.inner i) {k : ℕ} (hk : q ≤ k)
    (c : ℚ) (hc : 0 < c)
    (V : M → Set M) (hVopen : ∀ x, IsOpen (V x)) (hxV : ∀ x, x ∈ V x)
    (N : M → ℕ) (G : ∀ x, Fin (N x) → M → ℂ)
    (hGdiff : ∀ x i, MDifferentiableOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) (G x i) (V x))
    (R : M → M → ℝ)
    (hRbound : ∀ x, ∃ C : ℝ, ∀ y ∈ V x, |R x y| ≤ C)
    (hformula : ∀ x y, y ∈ V x →
      (regularizedMaxStageKahlerCurrent T hδ H.toRegularizedMaxCollarData hbranch k).potential y =
        ((c : ℝ) : EReal) * generatorLog (G x) y + (R x y : EReal))
    (hspan : ∀ x y, y ∈ V x → ∀ h : M → ℂ,
      IsInSpanAt (n := n) (· ∈ Set.range (G y)) y h ↔
        IsInSpanAt (n := n) (· ∈ Set.range (G x)) y h) :
    ∃ S : KahlerCurrent alpha,
      HasAnalyticSingularities (n := n) S.potential ∧
        HasManifoldSmoothAnalyticSingularities (n := n) S.potential ∧
        poleSet S.potential ⊆ {x | 0 < lelongNumber (n := n) T.potential x} := by
  apply exists_kahlerCurrent_poleSet_subset_lelongNumber_pos_of_regularizedMaxStage
    T hδ H hbranch hbranchtop hbranchsing halign hcover hk
  exact hasAnalyticSingularities_of_localGeneratorDescent c hc V hVopen hxV N G hGdiff
    R hRbound hformula hspan

end

end Hironaka.KahlerCurrentRegularizationRegularizedMax
