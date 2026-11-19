import Hironaka.Analytic.UniformLocalBergmanFiniteAtlas
import Hironaka.Analytic.KahlerCurrentRegularizationCollarBridge

set_option autoImplicit false

/-!
# Finite collar gluing of uniform Bergman patches

This file iterates the existing one-patch collar construction over a finite
uniform Bergman atlas.  Every collar and core comparison remains an explicit
hypothesis.  Thus it packages the formal finite gluing mechanism without
claiming the missing Demailly upper estimate which would produce those
comparisons from the weighted `L²` data.
-/

open Set Filter
open scoped Topology

namespace Hironaka.FiniteBergmanCollarGluing


open QuasiEquisingularBergmanAtlas
open QuasiEquisingularBergmanBranch
open QuasiEquisingularCollarGluing
open KahlerCurrentRegularizationBergmanBranch
open KahlerCurrentRegularizationCollarBridge

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- The sequential finite collar-glued candidate.  Stages beyond the finite
atlas count are unchanged, which makes induction on natural numbers convenient. -/
noncomputable def finiteBergmanGlued
    {θ : SmoothRealForm n M 2} {u : M → EReal} {m : ℕ}
    (A : FiniteUniformLocalBergmanAtlas θ u m) (g : M → EReal) : ℕ → M → EReal
  | 0 => g
  | k + 1 =>
      if hk : k < A.count then
        gluedMax ((A.patch ⟨k, hk⟩).patch.source : Set M)
          (bergmanBranch (A.patch ⟨k, hk⟩).patch) (finiteBergmanGlued A g k)
      else finiteBergmanGlued A g k

/-- The defining formula at a genuine atlas stage. -/
theorem finiteBergmanGlued_succ
    {θ : SmoothRealForm n M 2} {u : M → EReal} {m : ℕ}
    (A : FiniteUniformLocalBergmanAtlas θ u m) (g : M → EReal)
    {k : ℕ} (hk : k < A.count) :
    finiteBergmanGlued A g (k + 1) =
      gluedMax ((A.patch ⟨k, hk⟩).patch.source : Set M)
        (bergmanBranch (A.patch ⟨k, hk⟩).patch) (finiteBergmanGlued A g k) := by
  simp only [finiteBergmanGlued, dif_pos hk]

/-- The explicit collar and core comparisons required to perform every step
of the finite construction. -/
structure FiniteBergmanCollarData
    {θ : SmoothRealForm n M 2} {u : M → EReal} {m : ℕ}
    (A : FiniteUniformLocalBergmanAtlas θ u m) (g : M → EReal) where
  inner : Fin A.count → Set M
  inner_open : ∀ i, IsOpen (inner i)
  closure_inner_subset : ∀ i, closure (inner i) ⊆ (A.patch i).patch.source
  collar : ∀ i, ∀ x ∈ ((A.patch i).patch.source : Set M) \ inner i,
    bergmanBranch (A.patch i).patch x ≤ finiteBergmanGlued A g i.val x
  core : ∀ i, ∀ x ∈ inner i,
    finiteBergmanGlued A g i.val x ≤ bergmanBranch (A.patch i).patch x

/-- The collar maximum agrees locally with its global input at every point
outside the closure of the inner set.  This is the one-step preservation
mechanism used when later finite gluing steps avoid an earlier inner core. -/
theorem gluedMax_eventually_eq_global_of_not_mem_closure
    {U U' : Set M} {f g : M → EReal} (hU : IsOpen U)
    (hclosure : closure U' ⊆ U)
    (hcollar : ∀ x ∈ U \ U', f x ≤ g x) {x : M} (hx : x ∉ closure U') :
    gluedMax U f g =ᶠ[𝓝 x] g := by
  by_cases hxU : x ∈ U
  · have hxC : x ∈ (closure U')ᶜ := hx
    filter_upwards [hU.mem_nhds hxU,
      isClosed_closure.isOpen_compl.mem_nhds hxC] with y hyU hyC
    exact gluedMax_eq_global hcollar (fun hy' => hyC (subset_closure hy'))
  · exact gluedMax_eventually_eq_global hclosure hcollar hxU

/-- One later atlas step leaves a point unchanged as a germ whenever that
point lies outside the later inner-core closure. -/
theorem finiteBergmanGlued_eventuallyEq_succ_of_not_mem_closure
    {θ : SmoothRealForm n M 2} {u : M → EReal} {m : ℕ}
    (A : FiniteUniformLocalBergmanAtlas θ u m) (g : M → EReal)
    (H : FiniteBergmanCollarData A g) {k : ℕ} (hk : k < A.count)
    {x : M} (hx : x ∉ closure (H.inner ⟨k, hk⟩)) :
    finiteBergmanGlued A g (k + 1) =ᶠ[𝓝 x] finiteBergmanGlued A g k := by
  rw [finiteBergmanGlued_succ A g hk]
  exact gluedMax_eventually_eq_global_of_not_mem_closure
    (A.patch ⟨k, hk⟩).patch.source.isOpen (H.closure_inner_subset ⟨k, hk⟩)
    (H.collar ⟨k, hk⟩) hx

/-- If the inner core of patch `i` avoids all later inner-core closures, then
the candidate created at stage `i + 1` survives unchanged as a germ through
the final finite stage. -/
theorem finiteBergmanGlued_eventuallyEq_final_of_inner_avoids_later
    {θ : SmoothRealForm n M 2} {u : M → EReal} {m : ℕ}
    (A : FiniteUniformLocalBergmanAtlas θ u m) (g : M → EReal)
    (H : FiniteBergmanCollarData A g) (i : Fin A.count)
    {x : M} (hx : x ∈ H.inner i)
    (havoid : ∀ j : Fin A.count, i.val < j.val →
      H.inner i ⊆ (closure (H.inner j))ᶜ) :
    finiteBergmanGlued A g A.count =ᶠ[𝓝 x]
      finiteBergmanGlued A g (i.val + 1) := by
  have hstep : ∀ (k : ℕ), i.val < k → k < A.count →
      finiteBergmanGlued A g (k + 1) =ᶠ[𝓝 x] finiteBergmanGlued A g k := by
    intro k hik hk
    exact finiteBergmanGlued_eventuallyEq_succ_of_not_mem_closure A g H hk
      (havoid ⟨k, hk⟩ hik hx)
  have hprop : ∀ k, i.val + 1 ≤ k → k ≤ A.count →
      finiteBergmanGlued A g k =ᶠ[𝓝 x] finiteBergmanGlued A g (i.val + 1) := by
    intro k hik hk
    induction k, hik using Nat.le_induction with
    | base => exact EventuallyEq.rfl
    | succ k hik ih =>
        exact (hstep k (Nat.lt_of_succ_le hik) (Nat.lt_of_succ_le hk)).trans
          (ih (Nat.le_of_succ_le hk))
  exact hprop A.count (Nat.succ_le_of_lt i.isLt) le_rfl

/-- Under explicit stepwise collar data, every genuine finite stage is a
global theta-PSH potential. -/
theorem finiteBergmanGlued_isThetaPshPotential
    {θ : SmoothRealForm n M 2} {u : M → EReal} {m : ℕ}
    (A : FiniteUniformLocalBergmanAtlas θ u m) (g : M → EReal)
    (H : FiniteBergmanCollarData A g) (hm : 0 < m)
    (hg : IsThetaPshPotential θ g) :
    ∀ k ≤ A.count, IsThetaPshPotential θ (finiteBergmanGlued A g k) := by
  intro k hk
  induction k with
  | zero => simpa only [finiteBergmanGlued] using hg
  | succ k ih =>
      have hklt : k < A.count := Nat.lt_of_succ_le hk
      rw [finiteBergmanGlued_succ A g hklt]
      exact isThetaPshPotential_gluedMax (A.patch ⟨k, hklt⟩).patch.source.isOpen
        (H.closure_inner_subset ⟨k, hklt⟩) (H.collar ⟨k, hklt⟩)
        (bergmanBranch_thetaPlurisubharmonicOn (A.patch ⟨k, hklt⟩).patch hm)
        (ih (Nat.le_of_succ_le hk))

/-- At the stage in which a patch is glued, the global candidate has the
patch's analytic singularity type throughout its explicit inner core. -/
theorem finiteBergmanGlued_analyticTypeAt_core
    {θ : SmoothRealForm n M 2} {u : M → EReal} {m : ℕ}
    (A : FiniteUniformLocalBergmanAtlas θ u m) (g : M → EReal)
    (H : FiniteBergmanCollarData A g) (hm : 0 < m)
    (hg : IsThetaPshPotential θ g) (i : Fin A.count)
    {e : ComplexChart n M} {z : ComplexModel n} (hz : z ∈ e.val.target)
    (hzcore : e.val.symm z ∈ H.inner i) :
    HasAnalyticSingularityTypeAt
      (chartFunction (finiteBergmanGlued A g (i.val + 1)) e) z := by
  rw [finiteBergmanGlued_succ A g i.isLt]
  exact (gluedBergmanBranch_thetaPsh_analyticTypeAt (A.patch i).patch hm
    (H.inner_open i) (H.closure_inner_subset i) (H.collar i) (H.core i)
    (finiteBergmanGlued_isThetaPshPotential A g H hm hg i.val
      (Nat.le_of_lt i.isLt)) hz hzcore).2

/-- Any local lower bound for a patch Bergman branch transfers to the global
candidate at the stage where that patch is glued. -/
theorem finiteBergmanGlued_lowerBound_core
    {θ : SmoothRealForm n M 2} {u : M → EReal} {m : ℕ}
    (A : FiniteUniformLocalBergmanAtlas θ u m) (g : M → EReal)
    (H : FiniteBergmanCollarData A g) (i : Fin A.count)
    {q : M → EReal}
    (hq : ∀ x ∈ H.inner i, q x ≤ bergmanBranch (A.patch i).patch x) :
    ∀ x ∈ H.inner i, q x ≤ finiteBergmanGlued A g (i.val + 1) x := by
  intro x hx
  rw [finiteBergmanGlued_succ A g i.isLt, gluedMax_eq_max
    (H.closure_inner_subset i (subset_closure hx))]
  exact (hq x hx).trans (le_max_left _ _)

/-- Under explicit separation from all later inner-core closures, the local
analytic type produced at a patch stage persists to the final candidate. -/
theorem finiteBergmanGlued_analyticTypeAt_core_final
    {θ : SmoothRealForm n M 2} {u : M → EReal} {m : ℕ}
    (A : FiniteUniformLocalBergmanAtlas θ u m) (g : M → EReal)
    (H : FiniteBergmanCollarData A g) (hm : 0 < m)
    (hg : IsThetaPshPotential θ g) (i : Fin A.count)
    {e : ComplexChart n M} {z : ComplexModel n} (hz : z ∈ e.val.target)
    (hzcore : e.val.symm z ∈ H.inner i)
    (havoid : ∀ j : Fin A.count, i.val < j.val →
      H.inner i ⊆ (closure (H.inner j))ᶜ) :
    HasAnalyticSingularityTypeAt
      (chartFunction (finiteBergmanGlued A g A.count) e) z := by
  have hfinal := finiteBergmanGlued_eventuallyEq_final_of_inner_avoids_later
    A g H i hzcore havoid
  have hchart : chartFunction (finiteBergmanGlued A g A.count) e =ᶠ[𝓝 z]
      chartFunction (finiteBergmanGlued A g (i.val + 1)) e := by
    change (finiteBergmanGlued A g A.count ∘ e.val.symm) =ᶠ[𝓝 z]
      (finiteBergmanGlued A g (i.val + 1) ∘ e.val.symm)
    exact hfinal.comp_tendsto (e.val.continuousAt_symm hz)
  obtain ⟨c, N, f, hc, hf, b, hb, heq⟩ :=
    finiteBergmanGlued_analyticTypeAt_core A g H hm hg i hz hzcore
  exact ⟨c, N, f, hc, hf, b, hb, hchart.trans heq⟩

/-- The same separation transmits any lower bound from the `i`-th inner core
to a germwise lower bound for the final candidate. -/
theorem finiteBergmanGlued_eventually_lowerBound_core_final
    {θ : SmoothRealForm n M 2} {u : M → EReal} {m : ℕ}
    (A : FiniteUniformLocalBergmanAtlas θ u m) (g : M → EReal)
    (H : FiniteBergmanCollarData A g) (i : Fin A.count)
    {q : M → EReal}
    (hq : ∀ x ∈ H.inner i, q x ≤ bergmanBranch (A.patch i).patch x)
    {x : M} (hx : x ∈ H.inner i)
    (havoid : ∀ j : Fin A.count, i.val < j.val →
      H.inner i ⊆ (closure (H.inner j))ᶜ) :
    ∀ᶠ y in 𝓝 x, q y ≤ finiteBergmanGlued A g A.count y := by
  have hfinal := finiteBergmanGlued_eventuallyEq_final_of_inner_avoids_later
    A g H i hx havoid
  have hstage : ∀ y ∈ H.inner i,
      q y ≤ finiteBergmanGlued A g (i.val + 1) y :=
    finiteBergmanGlued_lowerBound_core A g H i hq
  filter_upwards [H.inner_open i |>.mem_nhds hx, hfinal] with y hy hEq
  rw [hEq]
  exact hstage y hy

end

end Hironaka.FiniteBergmanCollarGluing
