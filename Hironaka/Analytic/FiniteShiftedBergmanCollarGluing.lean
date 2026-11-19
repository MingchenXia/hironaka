import Hironaka.Analytic.FiniteBergmanCollarGluing
import Hironaka.Analytic.ShiftedBergmanBranch
import Hironaka.Analytic.BergmanBranchLowerComparison

set_option autoImplicit false

/-!
# Finite collar gluing of shifted Bergman branches

Finite real shifts allow the lower comparison of a local Bergman branch with a
previous global candidate to be recorded directly in finite collar data.  The
outer collar inequalities and separation of later cores remain explicit: this
is a finite conditional gluing mechanism, not a global Demailly sequence.
-/

open Set Filter
open scoped Topology

namespace Hironaka.FiniteShiftedBergmanCollarGluing


open DemaillyAnalyticType
open QuasiEquisingularBergmanAtlas
open QuasiEquisingularBergmanBranch
open QuasiEquisingularCollarGluing
open FiniteBergmanCollarGluing
open ShiftedBergmanBranch

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- The finite collar recursion using a specified real shift of each local
Bergman branch. -/
noncomputable def finiteShiftedBergmanGlued
    {θ : SmoothRealForm n M 2} {u : M → EReal} {m : ℕ}
    (A : FiniteUniformLocalBergmanAtlas θ u m) (offset : Fin A.count → ℝ)
    (g : M → EReal) : ℕ → M → EReal
  | 0 => g
  | k + 1 =>
      if hk : k < A.count then
        gluedMax ((A.patch ⟨k, hk⟩).patch.source : Set M)
          (shiftedBergmanBranch (A.patch ⟨k, hk⟩).patch (offset ⟨k, hk⟩))
          (finiteShiftedBergmanGlued A offset g k)
      else finiteShiftedBergmanGlued A offset g k

/-- The defining formula at a genuine shifted atlas stage. -/
theorem finiteShiftedBergmanGlued_succ
    {θ : SmoothRealForm n M 2} {u : M → EReal} {m : ℕ}
    (A : FiniteUniformLocalBergmanAtlas θ u m) (offset : Fin A.count → ℝ)
    (g : M → EReal) {k : ℕ} (hk : k < A.count) :
    finiteShiftedBergmanGlued A offset g (k + 1) =
      gluedMax ((A.patch ⟨k, hk⟩).patch.source : Set M)
        (shiftedBergmanBranch (A.patch ⟨k, hk⟩).patch (offset ⟨k, hk⟩))
        (finiteShiftedBergmanGlued A offset g k) := by
  simp only [finiteShiftedBergmanGlued, dif_pos hk]

/-- The explicit shifted collar and core comparisons required at every finite
step.  In particular, the missing outer Bergman estimate has not been hidden. -/
structure FiniteShiftedBergmanCollarData
    {θ : SmoothRealForm n M 2} {u : M → EReal} {m : ℕ}
    (A : FiniteUniformLocalBergmanAtlas θ u m) (offset : Fin A.count → ℝ)
    (g : M → EReal) where
  inner : Fin A.count → Set M
  inner_open : ∀ i, IsOpen (inner i)
  closure_inner_subset : ∀ i, closure (inner i) ⊆ (A.patch i).patch.source
  collar : ∀ i, ∀ x ∈ ((A.patch i).patch.source : Set M) \ inner i,
    shiftedBergmanBranch (A.patch i).patch (offset i) x ≤
      finiteShiftedBergmanGlued A offset g i.val x
  core : ∀ i, ∀ x ∈ inner i,
    finiteShiftedBergmanGlued A offset g i.val x ≤
      shiftedBergmanBranch (A.patch i).patch (offset i) x

/-- One shifted gluing step leaves a germ unchanged outside its inner-core
closure. -/
theorem finiteShiftedBergmanGlued_eventuallyEq_succ_of_not_mem_closure
    {θ : SmoothRealForm n M 2} {u : M → EReal} {m : ℕ}
    (A : FiniteUniformLocalBergmanAtlas θ u m) (offset : Fin A.count → ℝ)
    (g : M → EReal) (H : FiniteShiftedBergmanCollarData A offset g)
    {k : ℕ} (hk : k < A.count) {x : M}
    (hx : x ∉ closure (H.inner ⟨k, hk⟩)) :
    finiteShiftedBergmanGlued A offset g (k + 1) =ᶠ[𝓝 x]
      finiteShiftedBergmanGlued A offset g k := by
  rw [finiteShiftedBergmanGlued_succ A offset g hk]
  exact gluedMax_eventually_eq_global_of_not_mem_closure
    (A.patch ⟨k, hk⟩).patch.source.isOpen (H.closure_inner_subset ⟨k, hk⟩)
    (H.collar ⟨k, hk⟩) hx

/-- Under explicit stepwise shifted collar data, every genuine finite stage is
a global theta-PSH potential. -/
theorem finiteShiftedBergmanGlued_isThetaPshPotential
    {θ : SmoothRealForm n M 2} {u : M → EReal} {m : ℕ}
    (A : FiniteUniformLocalBergmanAtlas θ u m) (offset : Fin A.count → ℝ)
    (g : M → EReal) (H : FiniteShiftedBergmanCollarData A offset g)
    (hm : 0 < m) (hg : IsThetaPshPotential θ g) :
    ∀ k ≤ A.count, IsThetaPshPotential θ (finiteShiftedBergmanGlued A offset g k) := by
  intro k hk
  induction k with
  | zero => simpa only [finiteShiftedBergmanGlued] using hg
  | succ k ih =>
      have hklt : k < A.count := Nat.lt_of_succ_le hk
      rw [finiteShiftedBergmanGlued_succ A offset g hklt]
      exact isThetaPshPotential_gluedMax (A.patch ⟨k, hklt⟩).patch.source.isOpen
        (H.closure_inner_subset ⟨k, hklt⟩) (H.collar ⟨k, hklt⟩)
        (shiftedBergmanBranch_thetaPlurisubharmonicOn
          (A.patch ⟨k, hklt⟩).patch hm (offset ⟨k, hklt⟩))
        (ih (Nat.le_of_succ_le hk))

/-- A real shift preserves a branch's analytic singularity type in every
ambient chart meeting the patch source. -/
theorem shiftedBergmanBranch_analyticTypeAt
    {θ : SmoothRealForm n M 2} {u : M → EReal} {m : ℕ}
    (D : LocalBergmanPatch θ u m) (a : ℝ) (e : ComplexChart n M)
    {z : ComplexModel n} (hz : z ∈ e.val.target)
    (hzsource : e.val.symm z ∈ D.source) :
    HasAnalyticSingularityTypeAt (chartFunction (shiftedBergmanBranch D a) e) z := by
  refine HasAnalyticSingularityTypeAt.of_eventuallyEq_add_bounded
    (KahlerCurrentRegularizationBergmanBranch.bergmanBranch_analyticTypeAt D e hz hzsource)
    (b := fun _ => a) ?_ ?_
  · exact boundedRealGermAt_of_continuousAt continuousAt_const
  · exact Filter.Eventually.of_forall fun _ => by rfl

/-- A shifted Bergman branch has the CT22 smooth-remainder analytic
singularities in every chart meeting its source. -/
theorem shiftedBergmanBranch_smoothAnalyticSingularitiesAt
    {θ : SmoothRealForm n M 2} {u : M → EReal} {m : ℕ}
    (D : LocalBergmanPatch θ u m) (a : ℝ) (hm : 0 < m)
    (e : ComplexChart n M) {z : ComplexModel n} (hz : z ∈ e.val.target)
    (hzsource : e.val.symm z ∈ D.source) :
    HasSmoothAnalyticSingularitiesAt (chartFunction (shiftedBergmanBranch D a) e) z :=
  ShiftedBergmanBranch.shiftedBergmanBranch_smoothAnalyticSingularitiesAt
    D a hm e hz hzsource

/-- At its shifted gluing stage, the global candidate has the local analytic
type of the corresponding shifted Bergman branch throughout the inner core. -/
theorem finiteShiftedBergmanGlued_analyticTypeAt_core
    {θ : SmoothRealForm n M 2} {u : M → EReal} {m : ℕ}
    (A : FiniteUniformLocalBergmanAtlas θ u m) (offset : Fin A.count → ℝ)
    (g : M → EReal) (H : FiniteShiftedBergmanCollarData A offset g)
    (i : Fin A.count)
    {e : ComplexChart n M} {z : ComplexModel n} (hz : z ∈ e.val.target)
    (hzcore : e.val.symm z ∈ H.inner i) :
    HasAnalyticSingularityTypeAt
      (chartFunction (finiteShiftedBergmanGlued A offset g (i.val + 1)) e) z := by
  rw [finiteShiftedBergmanGlued_succ A offset g i.isLt]
  have hzsource : e.val.symm z ∈ (A.patch i).patch.source :=
    H.closure_inner_subset i (subset_closure hzcore)
  have hbranch := shiftedBergmanBranch_analyticTypeAt (A.patch i).patch (offset i)
    e hz hzsource
  have hcoreEq :
      gluedMax ((A.patch i).patch.source : Set M)
        (shiftedBergmanBranch (A.patch i).patch (offset i))
        (finiteShiftedBergmanGlued A offset g i.val) =ᶠ[𝓝 (e.val.symm z)]
      shiftedBergmanBranch (A.patch i).patch (offset i) := by
    filter_upwards [H.inner_open i |>.mem_nhds hzcore] with x hx
    rw [gluedMax_eq_max (H.closure_inner_subset i (subset_closure hx))]
    exact max_eq_left (H.core i x hx)
  have hchartEq :
      chartFunction
        (gluedMax ((A.patch i).patch.source : Set M)
          (shiftedBergmanBranch (A.patch i).patch (offset i))
          (finiteShiftedBergmanGlued A offset g i.val)) e =ᶠ[𝓝 z]
      chartFunction (shiftedBergmanBranch (A.patch i).patch (offset i)) e := by
    change (gluedMax ((A.patch i).patch.source : Set M)
      (shiftedBergmanBranch (A.patch i).patch (offset i))
      (finiteShiftedBergmanGlued A offset g i.val) ∘ e.val.symm) =ᶠ[𝓝 z]
      (shiftedBergmanBranch (A.patch i).patch (offset i) ∘ e.val.symm)
    exact hcoreEq.comp_tendsto (e.val.continuousAt_symm hz)
  obtain ⟨c, N, f, hc, hf, b, hb, heq⟩ := hbranch
  exact ⟨c, N, f, hc, hf, b, hb, hchartEq.trans heq⟩

/-- At its shifted gluing stage, the candidate has the strong analytic
singularities of the corresponding Bergman branch throughout the inner core. -/
theorem finiteShiftedBergmanGlued_smoothAnalyticSingularitiesAt_core
    {θ : SmoothRealForm n M 2} {u : M → EReal} {m : ℕ}
    (A : FiniteUniformLocalBergmanAtlas θ u m) (offset : Fin A.count → ℝ)
    (g : M → EReal) (H : FiniteShiftedBergmanCollarData A offset g)
    (hm : 0 < m) (i : Fin A.count)
    {e : ComplexChart n M} {z : ComplexModel n} (hz : z ∈ e.val.target)
    (hzcore : e.val.symm z ∈ H.inner i) :
    HasSmoothAnalyticSingularitiesAt
      (chartFunction (finiteShiftedBergmanGlued A offset g (i.val + 1)) e) z := by
  rw [finiteShiftedBergmanGlued_succ A offset g i.isLt]
  have hzsource : e.val.symm z ∈ (A.patch i).patch.source :=
    H.closure_inner_subset i (subset_closure hzcore)
  have hbranch := shiftedBergmanBranch_smoothAnalyticSingularitiesAt
    (A.patch i).patch (offset i) hm e hz hzsource
  have hcoreEq :
      gluedMax ((A.patch i).patch.source : Set M)
        (shiftedBergmanBranch (A.patch i).patch (offset i))
        (finiteShiftedBergmanGlued A offset g i.val) =ᶠ[𝓝 (e.val.symm z)]
      shiftedBergmanBranch (A.patch i).patch (offset i) := by
    filter_upwards [H.inner_open i |>.mem_nhds hzcore] with x hx
    rw [gluedMax_eq_max (H.closure_inner_subset i (subset_closure hx))]
    exact max_eq_left (H.core i x hx)
  have hchartEq :
      chartFunction
        (gluedMax ((A.patch i).patch.source : Set M)
          (shiftedBergmanBranch (A.patch i).patch (offset i))
          (finiteShiftedBergmanGlued A offset g i.val)) e =ᶠ[𝓝 z]
      chartFunction (shiftedBergmanBranch (A.patch i).patch (offset i)) e := by
    change (gluedMax ((A.patch i).patch.source : Set M)
      (shiftedBergmanBranch (A.patch i).patch (offset i))
      (finiteShiftedBergmanGlued A offset g i.val) ∘ e.val.symm) =ᶠ[𝓝 z]
      (shiftedBergmanBranch (A.patch i).patch (offset i) ∘ e.val.symm)
    exact hcoreEq.comp_tendsto (e.val.continuousAt_symm hz)
  obtain ⟨c, N, f, hc, hf, b, hb, heq⟩ := hbranch
  exact ⟨c, N, f, hc, hf, b, hb, hchartEq.trans heq⟩

/-- Any local lower bound for a shifted branch transfers to the global
candidate at the shifted patch stage. -/
theorem finiteShiftedBergmanGlued_lowerBound_core
    {θ : SmoothRealForm n M 2} {u : M → EReal} {m : ℕ}
    (A : FiniteUniformLocalBergmanAtlas θ u m) (offset : Fin A.count → ℝ)
    (g : M → EReal) (H : FiniteShiftedBergmanCollarData A offset g)
    (i : Fin A.count) {q : M → EReal}
    (hq : ∀ x ∈ H.inner i,
      q x ≤ shiftedBergmanBranch (A.patch i).patch (offset i) x) :
    ∀ x ∈ H.inner i,
      q x ≤ finiteShiftedBergmanGlued A offset g (i.val + 1) x := by
  intro x hx
  rw [finiteShiftedBergmanGlued_succ A offset g i.isLt, gluedMax_eq_max
    (H.closure_inner_subset i (subset_closure hx))]
  exact (hq x hx).trans (le_max_left _ _)

/-- If one shifted core avoids every later core closure, its successor stage
survives unchanged as a germ through the final finite stage. -/
theorem finiteShiftedBergmanGlued_eventuallyEq_final_of_inner_avoids_later
    {θ : SmoothRealForm n M 2} {u : M → EReal} {m : ℕ}
    (A : FiniteUniformLocalBergmanAtlas θ u m) (offset : Fin A.count → ℝ)
    (g : M → EReal) (H : FiniteShiftedBergmanCollarData A offset g)
    (i : Fin A.count) {x : M} (hx : x ∈ H.inner i)
    (havoid : ∀ j : Fin A.count, i.val < j.val →
      H.inner i ⊆ (closure (H.inner j))ᶜ) :
    finiteShiftedBergmanGlued A offset g A.count =ᶠ[𝓝 x]
      finiteShiftedBergmanGlued A offset g (i.val + 1) := by
  have hstep : ∀ (k : ℕ), i.val < k → k < A.count →
      finiteShiftedBergmanGlued A offset g (k + 1) =ᶠ[𝓝 x]
        finiteShiftedBergmanGlued A offset g k := by
    intro k hik hk
    exact finiteShiftedBergmanGlued_eventuallyEq_succ_of_not_mem_closure
      A offset g H hk (havoid ⟨k, hk⟩ hik hx)
  have hprop : ∀ k, i.val + 1 ≤ k → k ≤ A.count →
      finiteShiftedBergmanGlued A offset g k =ᶠ[𝓝 x]
        finiteShiftedBergmanGlued A offset g (i.val + 1) := by
    intro k hik hk
    induction k, hik using Nat.le_induction with
    | base => exact EventuallyEq.rfl
    | succ k hik ih =>
        exact (hstep k (Nat.lt_of_succ_le hik) (Nat.lt_of_succ_le hk)).trans
          (ih (Nat.le_of_succ_le hk))
  exact hprop A.count (Nat.succ_le_of_lt i.isLt) le_rfl

/-- The shifted branch's analytic type persists to the final finite candidate
whenever the inner core avoids all later inner-core closures. -/
theorem finiteShiftedBergmanGlued_analyticTypeAt_core_final
    {θ : SmoothRealForm n M 2} {u : M → EReal} {m : ℕ}
    (A : FiniteUniformLocalBergmanAtlas θ u m) (offset : Fin A.count → ℝ)
    (g : M → EReal) (H : FiniteShiftedBergmanCollarData A offset g)
    (i : Fin A.count)
    {e : ComplexChart n M} {z : ComplexModel n} (hz : z ∈ e.val.target)
    (hzcore : e.val.symm z ∈ H.inner i)
    (havoid : ∀ j : Fin A.count, i.val < j.val →
      H.inner i ⊆ (closure (H.inner j))ᶜ) :
    HasAnalyticSingularityTypeAt
      (chartFunction (finiteShiftedBergmanGlued A offset g A.count) e) z := by
  have hfinal := finiteShiftedBergmanGlued_eventuallyEq_final_of_inner_avoids_later
    A offset g H i hzcore havoid
  have hchart : chartFunction (finiteShiftedBergmanGlued A offset g A.count) e =ᶠ[𝓝 z]
      chartFunction (finiteShiftedBergmanGlued A offset g (i.val + 1)) e := by
    change (finiteShiftedBergmanGlued A offset g A.count ∘ e.val.symm) =ᶠ[𝓝 z]
      (finiteShiftedBergmanGlued A offset g (i.val + 1) ∘ e.val.symm)
    exact hfinal.comp_tendsto (e.val.continuousAt_symm hz)
  obtain ⟨c, N, f, hc, hf, b, hb, heq⟩ :=
    finiteShiftedBergmanGlued_analyticTypeAt_core A offset g H i hz hzcore
  exact ⟨c, N, f, hc, hf, b, hb, hchart.trans heq⟩

/-- If a core avoids all later core closures, its strong analytic
singularities persist to the final finite collar candidate. -/
theorem finiteShiftedBergmanGlued_smoothAnalyticSingularitiesAt_core_final
    {θ : SmoothRealForm n M 2} {u : M → EReal} {m : ℕ}
    (A : FiniteUniformLocalBergmanAtlas θ u m) (offset : Fin A.count → ℝ)
    (g : M → EReal) (H : FiniteShiftedBergmanCollarData A offset g)
    (hm : 0 < m) (i : Fin A.count)
    {e : ComplexChart n M} {z : ComplexModel n} (hz : z ∈ e.val.target)
    (hzcore : e.val.symm z ∈ H.inner i)
    (havoid : ∀ j : Fin A.count, i.val < j.val →
      H.inner i ⊆ (closure (H.inner j))ᶜ) :
    HasSmoothAnalyticSingularitiesAt
      (chartFunction (finiteShiftedBergmanGlued A offset g A.count) e) z := by
  have hfinal := finiteShiftedBergmanGlued_eventuallyEq_final_of_inner_avoids_later
    A offset g H i hzcore havoid
  have hchart : chartFunction (finiteShiftedBergmanGlued A offset g A.count) e =ᶠ[𝓝 z]
      chartFunction (finiteShiftedBergmanGlued A offset g (i.val + 1)) e := by
    change (finiteShiftedBergmanGlued A offset g A.count ∘ e.val.symm) =ᶠ[𝓝 z]
      (finiteShiftedBergmanGlued A offset g (i.val + 1) ∘ e.val.symm)
    exact hfinal.comp_tendsto (e.val.continuousAt_symm hz)
  obtain ⟨c, N, f, hc, hf, b, hb, heq⟩ :=
    finiteShiftedBergmanGlued_smoothAnalyticSingularitiesAt_core A offset g H hm i hz hzcore
  exact ⟨c, N, f, hc, hf, b, hb, hchart.trans heq⟩

/-- The same separation transmits shifted-branch lower bounds to a germwise
lower bound for the final finite candidate. -/
theorem finiteShiftedBergmanGlued_eventually_lowerBound_core_final
    {θ : SmoothRealForm n M 2} {u : M → EReal} {m : ℕ}
    (A : FiniteUniformLocalBergmanAtlas θ u m) (offset : Fin A.count → ℝ)
    (g : M → EReal) (H : FiniteShiftedBergmanCollarData A offset g)
    (i : Fin A.count) {q : M → EReal}
    (hq : ∀ x ∈ H.inner i,
      q x ≤ shiftedBergmanBranch (A.patch i).patch (offset i) x)
    {x : M} (hx : x ∈ H.inner i)
    (havoid : ∀ j : Fin A.count, i.val < j.val →
      H.inner i ⊆ (closure (H.inner j))ᶜ) :
    ∀ᶠ y in 𝓝 x, q y ≤ finiteShiftedBergmanGlued A offset g A.count y := by
  have hfinal := finiteShiftedBergmanGlued_eventuallyEq_final_of_inner_avoids_later
    A offset g H i hx havoid
  have hstage : ∀ y ∈ H.inner i,
      q y ≤ finiteShiftedBergmanGlued A offset g (i.val + 1) y :=
    finiteShiftedBergmanGlued_lowerBound_core A offset g H i hq
  filter_upwards [H.inner_open i |>.mem_nhds hx, hfinal] with y hy hEq
  rw [hEq]
  exact hstage y hy

/-- A predecessor bounded above by the original potential admits a finite
shift of the local Bergman branch which dominates it throughout the patch
source.  This supplies the core orientation; outer collar domination remains
separate data. -/
theorem exists_shiftedBergmanBranch_le_of_le_original_add
    {θ : SmoothRealForm n M 2} {u g : M → EReal} {m : ℕ}
    (D : LocalBergmanPatch θ u m) (hm : 0 < m) {B : ℝ}
    (hg : ∀ x ∈ D.source, g x ≤ u x + (B : EReal)) :
    ∃ a : ℝ, ∀ x ∈ D.source, g x ≤ shiftedBergmanBranch D a x := by
  obtain ⟨a, ha⟩ :=
    Hironaka.BergmanBranchLowerComparison.LocalBergmanPatch.exists_le_bergmanBranch_add_of_le_original_add D hm hg
  refine ⟨a, fun x hx => ?_⟩
  exact le_shiftedBergmanBranch_of_le_add_const D a (ha x hx)

end

end Hironaka.FiniteShiftedBergmanCollarGluing
