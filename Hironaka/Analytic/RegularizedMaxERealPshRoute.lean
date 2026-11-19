import Hironaka.Analytic.RegularizedMaxEReal
import Hironaka.Analytic.AnalyticGluingData

set_option autoImplicit false

/-!
# The PSH closure interface for an extended-real regularized maximum

`RegularizedMaxEReal.eregularizedMax` is an honest pointwise operation on
extended reals: it keeps exactly the common poles of its two inputs.  Its
pointwise algebra, however, cannot prove plurisubharmonicity through those
poles.  In particular, the real `C²` Hessian calculation applies only where
both branches are finite; it does not by itself give upper semicontinuity or
the disc submean inequality at a common pole.

This module isolates that analytic gap precisely.  `ThetaPshAcross θ w Z` is
not an assertion that `w` is globally theta-PSH: it asks only for the chart
PSH germs based at points of `Z`.  Together with the already-local
`ThetaPlurisubharmonicOn` criterion off `Z`, the assembly theorem proves the
global raw theta-PSH statement.  Applied to `eregularizedMax`, its natural
exceptional set is the common-pole set, proved here directly from the
pointwise definition.

Thus a later removable-singularity/upper-semicontinuous closure theorem has a
small, explicit target: construct `ThetaPshAcross` for this common-pole set.
No such analytic closure result is claimed in this file.
-/

open Set Filter
open scoped Topology

namespace Hironaka.RegularizedMaxERealPshRoute

open Hironaka.AnalyticGluingData
open RegularizedMaxEReal

noncomputable section

section Pointwise

variable {X : Type*}

/-- The locus where both inputs of an extended-real regularized maximum are
poles.  This is the only locus where the output is a pole. -/
def commonPoleSet (u v : X → EReal) : Set X := {x | u x = ⊥ ∧ v x = ⊥}

/-- The pointwise pole characterization, stated as membership in the
common-pole locus. -/
theorem mem_commonPoleSet_iff_eregularizedMax_eq_bot {δ : ℝ}
    (u v : X → EReal) (x : X) :
    x ∈ commonPoleSet u v ↔ eregularizedMax δ (u x) (v x) = ⊥ := by
  exact (eregularizedMax_eq_bot_iff δ (u x) (v x)).symm

/-- The common-pole set is exactly the pole set of the extended-real
regularized maximum, without any analytic regularity assumptions. -/
theorem commonPoleSet_eq_poleSet_eregularizedMax {δ : ℝ}
    (u v : X → EReal) :
    commonPoleSet u v = {x | eregularizedMax δ (u x) (v x) = ⊥} := by
  ext x
  exact mem_commonPoleSet_iff_eregularizedMax_eq_bot u v x

end Pointwise

section ThetaPshClosure

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- The missing local analytic assertion at a prescribed exceptional set.

This is deliberately the restriction of the *local* theta-PSH chart criterion
to points of `Z`.  It has no nondegeneracy field and says nothing at points
outside `Z`; hence it does not conceal a global theta-PSH conclusion. -/
def ThetaPshAcross (θ : SmoothRealForm n M 2) (w : M → EReal) (Z : Set M) : Prop :=
  ∀ e z, z ∈ e.val.target → e.val.symm z ∈ Z →
    ∃ W ρ, z ∈ W ∧ IsSmoothLocalPotential θ e W ρ ∧
      PlurisubharmonicOn (fun y => chartFunction w e y + (ρ y : EReal)) W

/-- A raw theta-PSH potential supplies the cross-set closure data on every
set. -/
theorem ThetaPlurisubharmonic.thetaPshAcross {θ : SmoothRealForm n M 2}
    {w : M → EReal} (hw : ThetaPlurisubharmonic θ w) (Z : Set M) :
    ThetaPshAcross θ w Z := by
  intro e z hz _
  exact hw e z hz

/-- Local theta-PSH data off a set plus the explicit local closure data on the
set are exactly equivalent to global raw theta-plurisubharmonicity. -/
theorem thetaPlurisubharmonic_iff_on_compl_and_across {θ : SmoothRealForm n M 2}
    {w : M → EReal} (Z : Set M) :
    ThetaPlurisubharmonic θ w ↔
      ThetaPlurisubharmonicOn θ w Zᶜ ∧ ThetaPshAcross θ w Z := by
  constructor
  · intro hw
    exact ⟨fun e z hz _ => hw e z hz, ThetaPlurisubharmonic.thetaPshAcross hw Z⟩
  · rintro ⟨hOff, hAcross⟩ e z hz
    by_cases hZ : e.val.symm z ∈ Z
    · exact hAcross e z hz hZ
    · exact hOff e z hz hZ

/-- The exact closure package needed to turn the extended-real regularized
maximum into a raw theta-PSH function.  Its first field concerns only the
complement of the common pole set; its second field is the genuine unresolved
cross-pole analytic step. -/
def ERegularizedMaxThetaPshClosure (θ : SmoothRealForm n M 2) (δ : ℝ)
    (u v : M → EReal) : Prop :=
  ThetaPlurisubharmonicOn θ
      (fun x => eregularizedMax δ (u x) (v x)) (commonPoleSet u v)ᶜ ∧
    ThetaPshAcross θ (fun x => eregularizedMax δ (u x) (v x)) (commonPoleSet u v)

/-- The closure package gives the global raw theta-PSH conclusion, and this
proof uses no smoothness or removable-singularity theorem beyond the package
fields themselves. -/
theorem ERegularizedMaxThetaPshClosure.thetaPlurisubharmonic
    {θ : SmoothRealForm n M 2} {δ : ℝ} {u v : M → EReal}
    (h : ERegularizedMaxThetaPshClosure θ δ u v) :
    ThetaPlurisubharmonic θ (fun x => eregularizedMax δ (u x) (v x)) :=
  (thetaPlurisubharmonic_iff_on_compl_and_across (θ := θ) (w := fun x =>
    eregularizedMax δ (u x) (v x)) (commonPoleSet u v)).mpr h

/-- A theta-PSH input never takes the value `⊤`; this gives the pointwise
upper-finiteness required by the extended-real regularized maximum bounds. -/
theorem ThetaPlurisubharmonic.ne_top {θ : SmoothRealForm n M 2}
    {w : M → EReal} (hw : ThetaPlurisubharmonic θ w) (x : M) : w x ≠ ⊤ :=
  hw.quasiPlurisubharmonic.ne_top x

/-- Each input lies below its extended-real regularized maximum when both
inputs are raw theta-PSH. -/
theorem le_eregularizedMax_left_of_thetaPlurisubharmonic
    {θ : SmoothRealForm n M 2} {δ : ℝ} {u v : M → EReal}
    (hδ : 0 < δ) (hu : ThetaPlurisubharmonic θ u)
    (hv : ThetaPlurisubharmonic θ v) (x : M) :
    u x ≤ eregularizedMax δ (u x) (v x) := by
  exact (le_max_left _ _).trans
    (max_le_eregularizedMax hδ (ThetaPlurisubharmonic.ne_top hu x)
      (ThetaPlurisubharmonic.ne_top hv x))

/-- Local nondegeneracy transfers from the left input to the extended-real
regularized maximum.  This is independent of the unresolved cross-pole PSH
closure step. -/
theorem locallyNondegenerate_eregularizedMax_left
    {θ : SmoothRealForm n M 2} {δ : ℝ} {u v : M → EReal}
    (hδ : 0 < δ) (hu : ThetaPlurisubharmonic θ u)
    (hv : ThetaPlurisubharmonic θ v) (hnd : LocallyNondegenerate u) :
    LocallyNondegenerate (fun x => eregularizedMax δ (u x) (v x)) := by
  intro x U hU hx
  obtain ⟨y, hyU, hyfin⟩ := hnd x U hU hx
  refine ⟨y, hyU, ?_⟩
  intro hybot
  apply hyfin
  apply le_bot_iff.mp
  simpa only [hybot] using
    le_eregularizedMax_left_of_thetaPlurisubharmonic hδ hu hv y

/-- **Conditional global PSH route for the extended-real regularized maximum.**

The hypotheses on `u` and `v` supply the finite-locus order control and the
nondegeneracy transfer.  `hClosure` is intentionally not discharged here: it
is the remaining analytic theorem, namely local PSH closure across the common
pole locus together with the finite-locus PSH construction. -/
theorem isThetaPshPotential_eregularizedMax_of_closure
    {θ : SmoothRealForm n M 2} {δ : ℝ} {u v : M → EReal}
    (hδ : 0 < δ) (hu : IsThetaPshPotential θ u)
    (hv : ThetaPlurisubharmonic θ v)
    (hClosure : ERegularizedMaxThetaPshClosure θ δ u v) :
    IsThetaPshPotential θ (fun x => eregularizedMax δ (u x) (v x)) :=
  ⟨hClosure.thetaPlurisubharmonic,
    locallyNondegenerate_eregularizedMax_left hδ hu.1 hv hu.2⟩

end ThetaPshClosure

end

end Hironaka.RegularizedMaxERealPshRoute
