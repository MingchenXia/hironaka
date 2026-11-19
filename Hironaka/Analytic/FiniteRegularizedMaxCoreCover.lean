import Hironaka.Analytic.FiniteRegularizedMaxCollarGluing

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The core cover erases the seed

`Hironaka.FiniteRegularizedMaxCollarGluing` carries the strong CT22 convention
through the regularized-max recursion, but its induction starts at the seed, so
it needs the seed to satisfy the convention too.  For Demailly regularization
that is fatal: the seed is the potential of the ARBITRARY Kähler current being
regularized, and "the seed already has smooth analytic singularities" is most of
the conclusion.

The shifted recursion avoids this with the `core` half of its collar data
together with a core cover: near any point some branch has already overwritten
the seed.  The same device works for the regularized maximum — but it needs the
STRICT gap `stage_i + δ ≤ branch i` on the core rather than `stage_i ≤ branch i`,
because `M_δ ≥ max` means a regularized maximum never discards a branch on a
non-strict inequality (I-0324).  `eregularizedMax_eq_right_of_gap` supplies
exactly that.

With `RegularizedMaxCoreData` and a cover, the final stage satisfies the strong
convention with NO hypothesis on the seed and NO hypothesis relating the seed to
the branches — and still no separation of cores, which is what distinguishes
this from the shifted recursion (I-0304).

**What instantiating this for real Bergman branches still needs**, by name:

* the strict `δ`-versions of the two comparisons.
  `Hironaka.FiniteShiftedBergmanCollarDataOfComparisons.finiteShiftedBergmanCollarData_of_compatible_comparisons`
  builds the non-strict collar/core pair from the branch comparisons; the
  regularized maximum needs `+ δ` on both sides (I-0324), which is a matter of
  enlarging the shift, not of new analysis;
* `hbranchsing` is not an assumption for real branches — it is proved by
  `Hironaka.ShiftedBergmanBranch.shiftedBergmanBranch_smoothAnalyticSingularitiesAt`;
* `PolewiseAlignedBranches` for overlapping Bergman charts, i.e. a common
  generator family at a common pole.  The machinery is
  `Hironaka.BergmanGeneratorFrameChange.exact_frameChange_generatorLog` and
  `Hironaka.AlignedBergmanFrameChange.AlignedBergmanBranchPresentation.frameChange`;
  no module assembles them into this predicate yet.
-/

open Set Filter
open scoped Topology

namespace Hironaka.FiniteRegularizedMaxCoreCover

open Hironaka
open Hironaka
open Hironaka.AnalyticGluingData
open Hironaka.NumericalRestrictedVolumeScaffold
open Hironaka.RegularizedMaxEReal
open Hironaka.RegularizedMaxSmoothAnalyticType
open Hironaka.RegularizedMaxCollarGluing
open Hironaka.FiniteRegularizedMaxCollarGluing

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- Collar data with the second, inner half of the comparison: on its core the
branch dominates the previous stage by the full scale `δ`. -/
structure RegularizedMaxCoreData (δ : ℝ) {q : ℕ} (U : Fin q → Set M)
    (branch : Fin q → M → EReal) (g : M → EReal)
    extends RegularizedMaxCollarData δ U branch g where
  inner_open : ∀ i, IsOpen (inner i)
  core : ∀ i : Fin q, ∀ x ∈ inner i,
    finiteRegularizedMaxGlued δ U branch g i.val x + (δ : EReal) ≤ branch i x

/-- **On its core, the stage immediately after patch `i` IS the branch.**  This
is where the seed disappears. -/
theorem finiteRegularizedMaxGlued_eq_branch_of_mem_core {δ : ℝ} (hδ : 0 < δ) {q : ℕ}
    {U : Fin q → Set M} {branch : Fin q → M → EReal} {g : M → EReal}
    (H : RegularizedMaxCoreData δ U branch g) (hbranchtop : ∀ i x, branch i x ≠ ⊤)
    (i : Fin q) {x : M} (hx : x ∈ H.inner i) :
    finiteRegularizedMaxGlued δ U branch g (i.val + 1) x = branch i x := by
  have hxU : x ∈ U i := H.closure_inner_subset i (subset_closure hx)
  rw [finiteRegularizedMaxGlued_succ δ U branch g i.isLt]
  have hi : (⟨i.val, i.isLt⟩ : Fin q) = i := rfl
  rw [hi, eregularizedMaxGlued_of_mem hxU]
  exact eregularizedMax_eq_right_of_gap hδ (H.core i x hx) (hbranchtop i x)

/-- The invariant the recursion propagates at one chart point: the stage has the
strong presentation, and at a pole it has it with the FIXED family `(c, F)`. -/
def StagePresentation (δ : ℝ) {q : ℕ} (U : Fin q → Set M) (branch : Fin q → M → EReal)
    (g : M → EReal) (e : ComplexChart n M) (z : ComplexModel n) (c : ℝ) {N : ℕ}
    (F : Fin N → ComplexModel n → ℂ) (j : ℕ) : Prop :=
  HasSmoothAnalyticSingularitiesAt
      (chartFunction (finiteRegularizedMaxGlued δ U branch g j) e) z ∧
    (chartFunction (finiteRegularizedMaxGlued δ U branch g j) e z = ⊥ →
      SmoothLogarithmicTypeAt
        (chartFunction (finiteRegularizedMaxGlued δ U branch g j) e) c F z)

/-- One step of the recursion preserves the invariant.  Only the branch clause of
the alignment is used; the seed plays no role. -/
theorem stagePresentation_succ {δ : ℝ} (hδ : 0 < δ) {q : ℕ} {U : Fin q → Set M}
    {branch : Fin q → M → EReal} {g : M → EReal}
    (H : RegularizedMaxCollarData δ U branch g)
    (hbranchtop : ∀ i x, branch i x ≠ ⊤) (hgtop : ∀ x, g x ≠ ⊤)
    (hbranchsing : ∀ (i : Fin q) (e : ComplexChart n M) (z : ComplexModel n),
      z ∈ e.val.target → e.val.symm z ∈ U i →
        HasSmoothAnalyticSingularitiesAt (chartFunction (branch i) e) z)
    {e : ComplexChart n M} {z : ComplexModel n} (hz : z ∈ e.val.target)
    {c : ℝ} {N : ℕ} {F : Fin N → ComplexModel n → ℂ}
    (hbal : ∀ i : Fin q, e.val.symm z ∈ U i → chartFunction (branch i) e z = ⊥ →
      SmoothLogarithmicTypeAt (chartFunction (branch i) e) c F z)
    {j : ℕ} (ih : StagePresentation δ U branch g e z c F j) :
    StagePresentation δ U branch g e z c F (j + 1) := by
  by_cases hj : j < q
  · rw [StagePresentation, finiteRegularizedMaxGlued_succ δ U branch g hj]
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
      refine ⟨HasSmoothAnalyticSingularitiesAt.congr_eventuallyEq
        (hasSmoothAnalyticSingularitiesAt_eregularizedMax hδ ih.1
          (hbranchsing ⟨j, hj⟩ e z hz hxU)
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
        (eregularizedMaxGlued_eventuallyEq_global hδ (H.closure_inner_subset ⟨j, hj⟩)
          (H.gap ⟨j, hj⟩) (finiteRegularizedMaxGlued_ne_top hbranchtop hgtop j)
          hxU).comp_tendsto (e.val.continuousAt_symm hz)
      exact ⟨HasSmoothAnalyticSingularitiesAt.congr_eventuallyEq ih.1 hglue,
        fun hbot => SmoothLogarithmicTypeAt.congr_eventuallyEq
          (ih.2 (by rw [← hglue.eq_of_nhds]; exact hbot)) hglue⟩
  · rw [StagePresentation, finiteRegularizedMaxGlued_of_not_lt δ U branch g hj]
    exact ih

/-- At each chart point, ONE coefficient and ONE generator family presents every
branch that is a pole there on whose patch the point lies.  Unlike
`Hironaka.FiniteRegularizedMaxCollarGluing.PolewiseAlignedOver` this says nothing
whatsoever about the seed. -/
def PolewiseAlignedBranches {q : ℕ} (U : Fin q → Set M) (branch : Fin q → M → EReal) :
    Prop :=
  ∀ (e : ComplexChart n M) (z : ComplexModel n), z ∈ e.val.target →
    ∃ (c : ℝ) (N : ℕ) (F : Fin N → ComplexModel n → ℂ),
      ∀ i : Fin q, e.val.symm z ∈ U i → chartFunction (branch i) e z = ⊥ →
        SmoothLogarithmicTypeAt (chartFunction (branch i) e) c F z

/-- **The final stage has the strong CT22 convention, with no hypothesis on the
seed.**  Compare
`Hironaka.FiniteShiftedBergmanGlobalAnalyticType.finiteShiftedBergmanGlued_hasManifoldSmoothAnalyticSingularities`,
which also asks nothing of the seed but additionally requires
`ShiftedLaterCoreSeparation`; here only the cover is needed. -/
theorem hasManifoldSmoothAnalyticSingularities_finiteRegularizedMaxGlued_of_coreCover
    {δ : ℝ} (hδ : 0 < δ) {q : ℕ} {U : Fin q → Set M} {branch : Fin q → M → EReal}
    {g : M → EReal} (H : RegularizedMaxCoreData δ U branch g)
    (hbranchtop : ∀ i x, branch i x ≠ ⊤) (hgtop : ∀ x, g x ≠ ⊤)
    (hbranchsing : ∀ (i : Fin q) (e : ComplexChart n M) (z : ComplexModel n),
      z ∈ e.val.target → e.val.symm z ∈ U i →
        HasSmoothAnalyticSingularitiesAt (chartFunction (branch i) e) z)
    (halign : PolewiseAlignedBranches (n := n) U branch)
    (hcover : ∀ x : M, ∃ i : Fin q, x ∈ H.inner i)
    {k : ℕ} (hk : q ≤ k) :
    HasManifoldSmoothAnalyticSingularities (n := n)
      (finiteRegularizedMaxGlued δ U branch g k) := by
  intro e z hz
  obtain ⟨c, N, F, hbal⟩ := halign e z hz
  obtain ⟨i₀, hi₀⟩ := hcover (e.val.symm z)
  have hxU : e.val.symm z ∈ U i₀ := H.closure_inner_subset i₀ (subset_closure hi₀)
  have hbase : StagePresentation δ U branch g e z c F (i₀.val + 1) := by
    have hO : IsOpen (e.val.target ∩ e.val.symm ⁻¹' H.inner i₀) :=
      e.val.continuousOn_symm.isOpen_inter_preimage e.val.open_target (H.inner_open i₀)
    have heq : chartFunction (finiteRegularizedMaxGlued δ U branch g (i₀.val + 1)) e
        =ᶠ[𝓝 z] chartFunction (branch i₀) e := by
      filter_upwards [hO.mem_nhds ⟨hz, hi₀⟩] with w hw
      exact finiteRegularizedMaxGlued_eq_branch_of_mem_core hδ H hbranchtop i₀ hw.2
    refine ⟨HasSmoothAnalyticSingularitiesAt.congr_eventuallyEq
      (hbranchsing i₀ e z hz hxU) heq, ?_⟩
    intro hbot
    rw [heq.eq_of_nhds] at hbot
    exact SmoothLogarithmicTypeAt.congr_eventuallyEq (hbal i₀ hxU hbot) heq
  have hmk : i₀.val + 1 ≤ k := le_trans i₀.isLt hk
  have hmain : ∀ j, i₀.val + 1 ≤ j → StagePresentation δ U branch g e z c F j := by
    intro j hj
    induction j, hj using Nat.le_induction with
    | base => exact hbase
    | succ j _ ih =>
        exact stagePresentation_succ hδ H.toRegularizedMaxCollarData hbranchtop hgtop
          hbranchsing hz hbal ih
  exact (hmain k hmk).1

end

end Hironaka.FiniteRegularizedMaxCoreCover
