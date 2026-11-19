import Hironaka.Analytic.FiniteRegularizedMaxCoreCover
import Hironaka.Analytic.RegularizedMaxOffPoleAppend

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The core-cover recursion in the `I-0489` convention: no alignment, one coefficient

`Hironaka.FiniteRegularizedMaxCoreCover.hasManifoldSmoothAnalyticSingularities_finiteRegularizedMaxGlued_of_coreCover`
carries the STRONG CT22 convention through the regularized-max recursion, and it
needs `PolewiseAlignedBranches`: at every chart point, one coefficient AND one
generator family presenting every branch that is a pole there.  Nothing in the
tree produces the family half, and it is genuinely hard — it is a frame change
between overlapping Bergman charts.

In the convention the human fixed in `I-0489` (`BoundedSmoothOffPoleLogarithmicTypeAt`:
bounded remainder, `C^∞` only off the pole set) the family half is not needed at
all.  `Hironaka.RegularizedMaxOffPoleAppend.boundedSmoothOffPoleLogarithmicTypeAt_eregularizedMax_append`
combines two branches with the CONCATENATED family `Fin.append F₁ F₂` and no
hypothesis whatsoever at a common pole.  What survives of the alignment is only
the coefficient: `Fin.append` merges families, not coefficients, so the whole
recursion must run at ONE fixed `c` — which for a level-`m` Bergman atlas is
`c = 1/m` and is available (`I-0508`).

That is the trade recorded here.  `BranchesOffPoleWithCoefficient` replaces the
pair (`hbranchsing`, `halign`) of the strong-convention theorem by the single
hypothesis that every branch has an `I-0489` presentation with that one `c`, and
the stage invariant `StageOffPolePresentation` loses its second clause entirely:
there is nothing to say at a pole.

Everything else — the core/collar data, the strict `δ`-gap that makes the
regularized maximum discard the previous stage on a core
(`finiteRegularizedMaxGlued_eq_branch_of_mem_core`), the cover that erases the
seed, the off-patch germ identity — is reused verbatim from the strong-convention
module; only the presentation predicate carried along the induction changes.
-/

open Set Filter
open scoped Topology ContDiff

namespace Hironaka.FiniteRegularizedMaxOffPoleCoreCover

open Hironaka
open Hironaka
open Hironaka.AnalyticGluingData
open Hironaka.NumericalRestrictedVolumeScaffold
open Hironaka.RegularizedMaxEReal
open Hironaka.RegularizedMaxCollarGluing
open Hironaka.FiniteRegularizedMaxCollarGluing
open Hironaka.FiniteRegularizedMaxCoreCover
open Hironaka.RegularizedMaxOffPoleAppend

noncomputable section

/-- The `I-0489` presentation depends on the function only through its germ. -/
theorem BoundedSmoothOffPoleLogarithmicTypeAt.congr_eventuallyEq {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E] {u w : E → EReal}
    {c : ℝ} {N : ℕ} {F : Fin N → E → ℂ} {z : E}
    (hu : BoundedSmoothOffPoleLogarithmicTypeAt u c F z) (h : w =ᶠ[𝓝 z] u) :
    BoundedSmoothOffPoleLogarithmicTypeAt w c F z := by
  obtain ⟨hc, hF, b, hb, hsm, heq⟩ := hu
  exact ⟨hc, hF, b, hb, hsm, h.trans heq⟩

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- **Every branch is presented in the `I-0489` convention with ONE fixed
coefficient `c`**, at every chart point of its own patch.

This is what replaces the pair (`hbranchsing`, `PolewiseAlignedBranches`) of the
strong-convention core-cover theorem.  The generator families are free — they may
differ from branch to branch and from point to point — because the regularized
maximum concatenates them.  Only the coefficient is shared, and only because
`Fin.append` cannot merge two different ones. -/
def BranchesOffPoleWithCoefficient (c : ℝ) {q : ℕ} (U : Fin q → Set M)
    (branch : Fin q → M → EReal) : Prop :=
  ∀ (i : Fin q) (e : ComplexChart n M) (z : ComplexModel n), z ∈ e.val.target →
    e.val.symm z ∈ U i →
      ∃ (N : ℕ) (F : Fin N → ComplexModel n → ℂ),
        BoundedSmoothOffPoleLogarithmicTypeAt (chartFunction (branch i) e) c F z

/-- The invariant the recursion propagates at one chart point: the stage has an
`I-0489` presentation with the fixed coefficient `c`.

Compare `Hironaka.FiniteRegularizedMaxCoreCover.StagePresentation`, which carries a
second clause describing the stage AT a pole with a fixed family.  Here there is
no second clause: the append theorem needs no hypothesis at a common pole. -/
def StageOffPolePresentation (δ : ℝ) {q : ℕ} (U : Fin q → Set M)
    (branch : Fin q → M → EReal) (g : M → EReal) (e : ComplexChart n M)
    (z : ComplexModel n) (c : ℝ) (j : ℕ) : Prop :=
  ∃ (N : ℕ) (F : Fin N → ComplexModel n → ℂ),
    BoundedSmoothOffPoleLogarithmicTypeAt
      (chartFunction (finiteRegularizedMaxGlued δ U branch g j) e) c F z

/-- One step of the recursion preserves the invariant.  On the patch the new stage
is the regularized maximum of the old stage and the branch, and the append theorem
presents it by the concatenated family; off the patch the stage is unchanged as a
germ.  The seed plays no role. -/
theorem stageOffPolePresentation_succ {δ : ℝ} (hδ : 0 < δ) {q : ℕ} {U : Fin q → Set M}
    {branch : Fin q → M → EReal} {g : M → EReal}
    (H : RegularizedMaxCollarData δ U branch g)
    (hbranchtop : ∀ i x, branch i x ≠ ⊤) (hgtop : ∀ x, g x ≠ ⊤)
    {c : ℝ} (hbranch : BranchesOffPoleWithCoefficient (n := n) c U branch)
    {e : ComplexChart n M} {z : ComplexModel n} (hz : z ∈ e.val.target)
    {j : ℕ} (ih : StageOffPolePresentation δ U branch g e z c j) :
    StageOffPolePresentation δ U branch g e z c (j + 1) := by
  by_cases hj : j < q
  · rw [StageOffPolePresentation, finiteRegularizedMaxGlued_succ δ U branch g hj]
    by_cases hxU : e.val.symm z ∈ U ⟨j, hj⟩
    · have hO : IsOpen (e.val.target ∩ e.val.symm ⁻¹' U ⟨j, hj⟩) :=
        e.val.continuousOn_symm.isOpen_inter_preimage e.val.open_target (H.source_open _)
      have heq : chartFunction
          (eregularizedMaxGlued (U ⟨j, hj⟩) δ (branch ⟨j, hj⟩)
            (finiteRegularizedMaxGlued δ U branch g j)) e =ᶠ[𝓝 z]
          fun y => eregularizedMax δ
            (chartFunction (finiteRegularizedMaxGlued δ U branch g j) e y)
            (chartFunction (branch ⟨j, hj⟩) e y) := by
        filter_upwards [hO.mem_nhds ⟨hz, hxU⟩] with w hw
        exact eregularizedMaxGlued_of_mem hw.2
      obtain ⟨N₁, F₁, hstage⟩ := ih
      obtain ⟨N₂, F₂, hbr⟩ := hbranch ⟨j, hj⟩ e z hz hxU
      exact ⟨N₁ + N₂, Fin.append F₁ F₂,
        BoundedSmoothOffPoleLogarithmicTypeAt.congr_eventuallyEq
          (boundedSmoothOffPoleLogarithmicTypeAt_eregularizedMax_append hδ hstage hbr) heq⟩
    · have hglue : chartFunction
          (eregularizedMaxGlued (U ⟨j, hj⟩) δ (branch ⟨j, hj⟩)
            (finiteRegularizedMaxGlued δ U branch g j)) e =ᶠ[𝓝 z]
          chartFunction (finiteRegularizedMaxGlued δ U branch g j) e :=
        (eregularizedMaxGlued_eventuallyEq_global hδ (H.closure_inner_subset ⟨j, hj⟩)
          (H.gap ⟨j, hj⟩) (finiteRegularizedMaxGlued_ne_top hbranchtop hgtop j)
          hxU).comp_tendsto (e.val.continuousAt_symm hz)
      obtain ⟨N₁, F₁, hstage⟩ := ih
      exact ⟨N₁, F₁,
        BoundedSmoothOffPoleLogarithmicTypeAt.congr_eventuallyEq hstage hglue⟩
  · rw [StageOffPolePresentation, finiteRegularizedMaxGlued_of_not_lt δ U branch g hj]
    exact ih

/-- **The final stage is presented at every chart point with the SAME coefficient
`c`.**  This is the fixed-coefficient form of the core-cover conclusion: the
generator family still depends on the point, but the logarithmic coefficient
does not, and it is the coefficient supplied by
`BranchesOffPoleWithCoefficient`.  The existential-coefficient statement below
is the immediate corollary. -/
theorem stageOffPolePresentation_of_coreCover
    {δ : ℝ} (hδ : 0 < δ) {q : ℕ} {U : Fin q → Set M} {branch : Fin q → M → EReal}
    {g : M → EReal} (H : RegularizedMaxCoreData δ U branch g)
    (hbranchtop : ∀ i x, branch i x ≠ ⊤) (hgtop : ∀ x, g x ≠ ⊤)
    {c : ℝ} (hbranch : BranchesOffPoleWithCoefficient (n := n) c U branch)
    (hcover : ∀ x : M, ∃ i : Fin q, x ∈ H.inner i)
    {k : ℕ} (hk : q ≤ k) (e : ComplexChart n M) {z : ComplexModel n}
    (hz : z ∈ e.val.target) :
    StageOffPolePresentation δ U branch g e z c k := by
  obtain ⟨i₀, hi₀⟩ := hcover (e.val.symm z)
  have hxU : e.val.symm z ∈ U i₀ := H.closure_inner_subset i₀ (subset_closure hi₀)
  have hbase : StageOffPolePresentation δ U branch g e z c (i₀.val + 1) := by
    have hO : IsOpen (e.val.target ∩ e.val.symm ⁻¹' H.inner i₀) :=
      e.val.continuousOn_symm.isOpen_inter_preimage e.val.open_target (H.inner_open i₀)
    have heq : chartFunction (finiteRegularizedMaxGlued δ U branch g (i₀.val + 1)) e
        =ᶠ[𝓝 z] chartFunction (branch i₀) e := by
      filter_upwards [hO.mem_nhds ⟨hz, hi₀⟩] with w hw
      exact finiteRegularizedMaxGlued_eq_branch_of_mem_core hδ H hbranchtop i₀ hw.2
    obtain ⟨N, F, hbr⟩ := hbranch i₀ e z hz hxU
    exact ⟨N, F, BoundedSmoothOffPoleLogarithmicTypeAt.congr_eventuallyEq hbr heq⟩
  have hmk : i₀.val + 1 ≤ k := le_trans i₀.isLt hk
  have hmain : ∀ j, i₀.val + 1 ≤ j → StageOffPolePresentation δ U branch g e z c j := by
    intro j hj
    induction j, hj using Nat.le_induction with
    | base => exact hbase
    | succ j _ ih =>
        exact stageOffPolePresentation_succ hδ H.toRegularizedMaxCollarData hbranchtop
          hgtop hbranch hz ih
  exact hmain k hmk

/-- **The final stage has analytic singularities in the `I-0489` convention, with no
hypothesis on the seed and NO alignment of generator families.**

This is the off-pole analogue of
`Hironaka.FiniteRegularizedMaxCoreCover.hasManifoldSmoothAnalyticSingularities_finiteRegularizedMaxGlued_of_coreCover`,
and it is the statement that removes `PolewiseAlignedBranches` — the one
obligation of the regularized-max route that no module in the tree produces —
from the road to Demailly regularization.  What it costs is the single common
coefficient in `BranchesOffPoleWithCoefficient`. -/
theorem hasManifoldAnalyticSingularitiesSmoothOffPole_finiteRegularizedMaxGlued_of_coreCover
    {δ : ℝ} (hδ : 0 < δ) {q : ℕ} {U : Fin q → Set M} {branch : Fin q → M → EReal}
    {g : M → EReal} (H : RegularizedMaxCoreData δ U branch g)
    (hbranchtop : ∀ i x, branch i x ≠ ⊤) (hgtop : ∀ x, g x ≠ ⊤)
    {c : ℝ} (hbranch : BranchesOffPoleWithCoefficient (n := n) c U branch)
    (hcover : ∀ x : M, ∃ i : Fin q, x ∈ H.inner i)
    {k : ℕ} (hk : q ≤ k) :
    HasManifoldAnalyticSingularitiesSmoothOffPole (n := n)
      (finiteRegularizedMaxGlued δ U branch g k) := by
  intro e z hz
  obtain ⟨N, F, hF⟩ :=
    stageOffPolePresentation_of_coreCover hδ H hbranchtop hgtop hbranch hcover hk e hz
  exact ⟨c, N, F, hF⟩

end

end Hironaka.FiniteRegularizedMaxOffPoleCoreCover
