import Hironaka.Analytic.RegularizedMaxCollarGluing

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The finite atlas stage of Demailly regularization, glued by `M_δ`

This is the finite recursion of
`Hironaka.FiniteShiftedBergmanCollarGluing.finiteShiftedBergmanGlued` with the
ordinary maximum replaced by the regularized maximum, and it is what makes the
strong CT22 convention reachable for a genuine multi-chart atlas.

The shifted recursion proves its strong-convention output only under
`ShiftedLaterCoreSeparation` — every core avoids the closure of all later cores
— together with a core cover; on a connected manifold those two hypotheses
force `A.count = 1`, so that endpoint is not instantiable for an atlas with more
than one patch (I-0304).  Here there is no separation hypothesis at all, and no
core cover: the recursion never needs to erase the seed, because at every stage
the strong presentation is preserved *pointwise*, either as the previous stage's
(off the current core) or as the aligned merge of the two.

The one hypothesis that replaces the whole separation apparatus is
`PolewiseAlignedOver`: at each chart point, ONE coefficient and ONE generator
family presents the seed and every branch whose patch contains the point and
which is a pole there.  That is a statement about local generators of the
multiplier ideal, not an analytic estimate.

**Caveat, and where to go instead.**  The induction below starts at the seed and
no step ever discards it, so `hasManifoldSmoothAnalyticSingularities_finiteRegularizedMaxGlued`
asks the seed to satisfy the strong convention as well — through `hg` and through
the seed clause of `PolewiseAlignedOver`.  For Demailly regularization the seed
is the potential of the arbitrary Kähler current being regularized, so that is
not available.  `Hironaka.FiniteRegularizedMaxCoreCover` removes both by adding
the inner half of the collar comparison (`core`) and a core cover, which is how
the shifted recursion erases its seed too; the statement here is the one to use
when there is no cover.
-/

open Set Filter
open scoped Topology

namespace Hironaka.FiniteRegularizedMaxCollarGluing

open Hironaka
open Hironaka
open Hironaka.AnalyticGluingData
open Hironaka.NumericalRestrictedVolumeScaffold
open Hironaka.RegularizedMaxEReal
open Hironaka.RegularizedMaxSmoothAnalyticType
open Hironaka.RegularizedMaxCollarGluing

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- The finite collar recursion driven by the regularized maximum. -/
def finiteRegularizedMaxGlued (δ : ℝ) {q : ℕ} (U : Fin q → Set M)
    (branch : Fin q → M → EReal) (g : M → EReal) : ℕ → M → EReal
  | 0 => g
  | k + 1 =>
      if hk : k < q then
        eregularizedMaxGlued (U ⟨k, hk⟩) δ (branch ⟨k, hk⟩)
          (finiteRegularizedMaxGlued δ U branch g k)
      else finiteRegularizedMaxGlued δ U branch g k

theorem finiteRegularizedMaxGlued_succ (δ : ℝ) {q : ℕ} (U : Fin q → Set M)
    (branch : Fin q → M → EReal) (g : M → EReal) {k : ℕ} (hk : k < q) :
    finiteRegularizedMaxGlued δ U branch g (k + 1) =
      eregularizedMaxGlued (U ⟨k, hk⟩) δ (branch ⟨k, hk⟩)
        (finiteRegularizedMaxGlued δ U branch g k) := by
  simp only [finiteRegularizedMaxGlued, dif_pos hk]

theorem finiteRegularizedMaxGlued_of_not_lt (δ : ℝ) {q : ℕ} (U : Fin q → Set M)
    (branch : Fin q → M → EReal) (g : M → EReal) {k : ℕ} (hk : ¬ k < q) :
    finiteRegularizedMaxGlued δ U branch g (k + 1) =
      finiteRegularizedMaxGlued δ U branch g k := by
  simp only [finiteRegularizedMaxGlued, dif_neg hk]

/-- No stage takes the value `⊤` if the seed and the branches do not. -/
theorem finiteRegularizedMaxGlued_ne_top {δ : ℝ} {q : ℕ} {U : Fin q → Set M}
    {branch : Fin q → M → EReal} {g : M → EReal}
    (hbranch : ∀ i x, branch i x ≠ ⊤) (hg : ∀ x, g x ≠ ⊤) (k : ℕ) (x : M) :
    finiteRegularizedMaxGlued δ U branch g k x ≠ ⊤ := by
  induction k generalizing x with
  | zero => exact hg x
  | succ k ih =>
      by_cases hk : k < q
      · rw [finiteRegularizedMaxGlued_succ δ U branch g hk]
        by_cases hx : x ∈ U ⟨k, hk⟩
        · rw [eregularizedMaxGlued_of_mem hx]
          exact eregularizedMax_ne_top (ih x) (hbranch _ x)
        · rw [eregularizedMaxGlued_of_not_mem hx]
          exact ih x
      · rw [finiteRegularizedMaxGlued_of_not_lt δ U branch g hk]
        exact ih x

/-- The finite regularized-max recursion never lowers its initial seed.

This is the pointwise fact needed for the Lelong-number comparison in the
Kähler-current regularization endpoint: a larger potential has no larger
Lelong number.  It uses the finite-value hypotheses only to apply the
extended-real regularized-max lower bound at an active collar stage. -/
theorem seed_le_finiteRegularizedMaxGlued {δ : ℝ} (hδ : 0 < δ)
    {q : ℕ} {U : Fin q → Set M} {branch : Fin q → M → EReal} {g : M → EReal}
    (hbranch : ∀ i x, branch i x ≠ ⊤) (hg : ∀ x, g x ≠ ⊤) (k : ℕ) (x : M) :
    g x ≤ finiteRegularizedMaxGlued δ U branch g k x := by
  induction k generalizing x with
  | zero => exact le_rfl
  | succ k ih =>
      by_cases hk : k < q
      · rw [finiteRegularizedMaxGlued_succ δ U branch g hk]
        exact (ih x).trans (le_eregularizedMaxGlued hδ
          (fun y _ => hbranch ⟨k, hk⟩ y)
          (finiteRegularizedMaxGlued_ne_top hbranch hg k) x)
      · rw [finiteRegularizedMaxGlued_of_not_lt δ U branch g hk]
        exact ih x

/-- The stepwise collar data of the recursion.  `gap` is the scale-`δ`
strengthening of the ordinary collar inequality; it is what makes the glue equal
to the previous stage off the core. -/
structure RegularizedMaxCollarData (δ : ℝ) {q : ℕ} (U : Fin q → Set M)
    (branch : Fin q → M → EReal) (g : M → EReal) where
  source_open : ∀ i, IsOpen (U i)
  inner : Fin q → Set M
  closure_inner_subset : ∀ i, closure (inner i) ⊆ U i
  gap : ∀ i : Fin q, ∀ x ∈ U i \ inner i,
    branch i x + (δ : EReal) ≤ finiteRegularizedMaxGlued δ U branch g i.val x

/-- **Every stage is a theta-PSH potential in the same background.**  No
curvature is lost and no core cover is needed. -/
theorem isThetaPshPotential_finiteRegularizedMaxGlued {θ : SmoothRealForm n M 2}
    {δ : ℝ} (hδ : 0 < δ) {q : ℕ} {U : Fin q → Set M} {branch : Fin q → M → EReal}
    {g : M → EReal} (H : RegularizedMaxCollarData δ U branch g)
    (hbranch : ∀ i, ThetaPlurisubharmonicOn θ (branch i) (U i))
    (hg : IsThetaPshPotential θ g) (k : ℕ) :
    IsThetaPshPotential θ (finiteRegularizedMaxGlued δ U branch g k) := by
  induction k with
  | zero => exact hg
  | succ k ih =>
      by_cases hk : k < q
      · rw [finiteRegularizedMaxGlued_succ δ U branch g hk]
        exact isThetaPshPotential_eregularizedMaxGlued hδ (H.source_open _)
          (H.closure_inner_subset ⟨k, hk⟩) (H.gap ⟨k, hk⟩) (hbranch ⟨k, hk⟩) ih
      · rw [finiteRegularizedMaxGlued_of_not_lt δ U branch g hk]
        exact ih


/-- The strong local presentation is a germ property. -/
theorem SmoothLogarithmicTypeAt.congr_eventuallyEq {c : ℝ} {N : ℕ}
    {u w : ComplexModel n → EReal} {F : Fin N → ComplexModel n → ℂ}
    {z : ComplexModel n} (hu : SmoothLogarithmicTypeAt u c F z) (h : w =ᶠ[𝓝 z] u) :
    SmoothLogarithmicTypeAt w c F z := by
  obtain ⟨hc, hF, b, hb, heq⟩ := hu
  exact ⟨hc, hF, b, hb, h.trans heq⟩

/-- At each chart point, ONE coefficient and ONE generator family presents the
seed and every branch that is a pole there on whose patch the point lies.  This
is the entire residual hypothesis of the strong-convention finite gluing. -/
def PolewiseAlignedOver {q : ℕ} (U : Fin q → Set M) (branch : Fin q → M → EReal)
    (g : M → EReal) : Prop :=
  ∀ (e : ComplexChart n M) (z : ComplexModel n), z ∈ e.val.target →
    ∃ (c : ℝ) (N : ℕ) (F : Fin N → ComplexModel n → ℂ),
      (chartFunction g e z = ⊥ → SmoothLogarithmicTypeAt (chartFunction g e) c F z) ∧
      ∀ i : Fin q, e.val.symm z ∈ U i → chartFunction (branch i) e z = ⊥ →
        SmoothLogarithmicTypeAt (chartFunction (branch i) e) c F z

/-- **Every stage keeps the strong CT22 convention.**  Compare
`Hironaka.FiniteShiftedBergmanGlobalAnalyticType.finiteShiftedBergmanGlued_hasManifoldSmoothAnalyticSingularities`,
which needs `ShiftedLaterCoreSeparation` and a core cover: here neither appears,
so the statement is instantiable for a genuine multi-chart atlas. -/
theorem hasManifoldSmoothAnalyticSingularities_finiteRegularizedMaxGlued {δ : ℝ}
    (hδ : 0 < δ) {q : ℕ} {U : Fin q → Set M} {branch : Fin q → M → EReal}
    {g : M → EReal} (H : RegularizedMaxCollarData δ U branch g)
    (hbranchtop : ∀ i x, branch i x ≠ ⊤) (hgtop : ∀ x, g x ≠ ⊤)
    (hg : HasManifoldSmoothAnalyticSingularities (n := n) g)
    (hbranch : ∀ (i : Fin q) (e : ComplexChart n M) (z : ComplexModel n),
      z ∈ e.val.target → e.val.symm z ∈ U i →
        HasSmoothAnalyticSingularitiesAt (chartFunction (branch i) e) z)
    (halign : PolewiseAlignedOver (n := n) U branch g) (k : ℕ) :
    HasManifoldSmoothAnalyticSingularities (n := n)
      (finiteRegularizedMaxGlued δ U branch g k) := by
  intro e z hz
  obtain ⟨c, N, F, hgal, hbal⟩ := halign e z hz
  suffices h : ∀ j : ℕ,
      HasSmoothAnalyticSingularitiesAt
          (chartFunction (finiteRegularizedMaxGlued δ U branch g j) e) z ∧
        (chartFunction (finiteRegularizedMaxGlued δ U branch g j) e z = ⊥ →
          SmoothLogarithmicTypeAt
            (chartFunction (finiteRegularizedMaxGlued δ U branch g j) e) c F z) from (h k).1
  intro j
  induction j with
  | zero => exact ⟨hg e z hz, hgal⟩
  | succ j ih =>
      by_cases hj : j < q
      · rw [finiteRegularizedMaxGlued_succ δ U branch g hj]
        by_cases hxU : e.val.symm z ∈ U ⟨j, hj⟩
        · have hO : IsOpen (e.val.target ∩ e.val.symm ⁻¹' U ⟨j, hj⟩) :=
            e.val.continuousOn_symm.isOpen_inter_preimage e.val.open_target
              (H.source_open _)
          have heq : chartFunction
              (eregularizedMaxGlued (U ⟨j, hj⟩) δ (branch ⟨j, hj⟩)
                (finiteRegularizedMaxGlued δ U branch g j)) e =ᶠ[𝓝 z]
              fun y => eregularizedMax δ
                (chartFunction (finiteRegularizedMaxGlued δ U branch g j) e y)
                (chartFunction (branch ⟨j, hj⟩) e y) := by
            filter_upwards [hO.mem_nhds ⟨hz, hxU⟩] with w hw
            exact eregularizedMaxGlued_of_mem hw.2
          refine ⟨HasSmoothAnalyticSingularitiesAt.congr_eventuallyEq
            (hasSmoothAnalyticSingularitiesAt_eregularizedMax hδ ih.1
              (hbranch ⟨j, hj⟩ e z hz hxU)
              (fun h₁ h₂ => ⟨c, N, F, ih.2 h₁, hbal _ hxU h₂⟩)) heq, ?_⟩
          intro hbot
          rw [heq.eq_of_nhds] at hbot
          obtain ⟨h₁, h₂⟩ := (eregularizedMax_eq_bot_iff δ _ _).mp hbot
          exact SmoothLogarithmicTypeAt.congr_eventuallyEq
            (SmoothLogarithmicTypeAt.eregularizedMax_of_aligned (ih.2 h₁) (hbal _ hxU h₂)) heq
        · have hglue : chartFunction
              (eregularizedMaxGlued (U ⟨j, hj⟩) δ (branch ⟨j, hj⟩)
                (finiteRegularizedMaxGlued δ U branch g j)) e =ᶠ[𝓝 z]
              chartFunction (finiteRegularizedMaxGlued δ U branch g j) e :=
            (eregularizedMaxGlued_eventuallyEq_global hδ
              (H.closure_inner_subset ⟨j, hj⟩) (H.gap ⟨j, hj⟩)
              (finiteRegularizedMaxGlued_ne_top hbranchtop hgtop j)
              hxU).comp_tendsto (e.val.continuousAt_symm hz)
          exact ⟨HasSmoothAnalyticSingularitiesAt.congr_eventuallyEq ih.1 hglue,
            fun hbot => SmoothLogarithmicTypeAt.congr_eventuallyEq
              (ih.2 (by rw [← hglue.eq_of_nhds]; exact hbot)) hglue⟩
      · rw [finiteRegularizedMaxGlued_of_not_lt δ U branch g hj]
        exact ih

end

end Hironaka.FiniteRegularizedMaxCollarGluing
