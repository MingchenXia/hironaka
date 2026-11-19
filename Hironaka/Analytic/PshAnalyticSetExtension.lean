import Hironaka.Analytic.ThetaPshCodimTwoExtension
import Hironaka.Analytic.AnalyticSubsetTopology

set_option autoImplicit false

/-!
# The analytic-set removable-singularity interface for theta-PSH functions

Step 3 of the quantitative Demailly regularization constructs a function
which is theta-PSH away from the zero locus `A` of a multiplier ideal, locally
bounded above there, and tends to `-∞` along `A`.  The only unformalized
analytic input in that step is the Grauert--Remmert theorem which turns those
facts into local theta-PSH germs at points of `A`.

This file does not postulate that global conclusion.  It records the precise
local closure statement and proves the surrounding topological bookkeeping:

* the upper regularization of a function tending to `-∞` along `A` agrees
  with its prescribed pole-valued representative;
* theta-PSH off `A`, together with that local closure statement only at points
  of `A`, gives global theta-PSH;
* the already formalized codimension-two flattening theorem discharges the
  local statement in that special case.

Thus the remaining general theorem is exactly the local removable-singularity
argument for a proper analytic set (including its hypersurface part), rather
than a hidden global regularity field.
-/

open Set Filter
open scoped Topology

namespace Hironaka.PshAnalyticSetExtension


open ThetaPshCodimTwoExtension

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

variable {A : Set M} {theta : SmoothRealForm n M 2} {u : M → EReal}

/-- The local bounded-above hypothesis in the Grauert--Remmert extension
theorem, stated only off the exceptional set. -/
def LocallyBoundedAboveOff (A : Set M) (u : M → EReal) : Prop :=
  ∀ x : M, ∃ U : Set M, U ∈ 𝓝 x ∧ ∃ C : ℝ, ∀ y ∈ U, y ∉ A → u y ≤ (C : EReal)

/-- The branch values approach `-∞` from the complement of the exceptional
set.  This is the extra fact available for the regularized Bergman maximum in
the manuscript. -/
def TendsToBotOff (A : Set M) (u : M → EReal) : Prop :=
  ∀ x ∈ A, ∀ C : ℝ, ∀ᶠ y in 𝓝 x, y ∉ A → u y < (C : EReal)

/-- The local conclusion supplied by a removable-singularity theorem.  It is
restricted to chart points over `A`; no global theta-PSH conclusion is stored
in this predicate. -/
def ThetaPshLocalClosure (theta : SmoothRealForm n M 2) (A : Set M)
    (u : M → EReal) : Prop :=
  ∀ e z, z ∈ e.val.target → e.val.symm z ∈ A →
    ∃ W rho, z ∈ W ∧ IsSmoothLocalPotential theta e W rho ∧
      PlurisubharmonicOn
        (fun y => chartFunction (extensionAcross A u) e y + (rho y : EReal)) W

/-- At a point of `A`, the upper regularization is `-∞` when the off-set
branch tends to `-∞`. -/
theorem extensionAcross_eq_bot_of_tendsToBotOff (htend : TendsToBotOff A u)
    {x : M} (hx : x ∈ A) :
    extensionAcross A u x = ⊥ := by
  classical
  apply (EReal.eq_bot_iff_forall_lt _).mpr
  intro C
  have hU : {y | (if y ∈ A then (⊥ : EReal) else u y) ≤ ((C - 1 : ℝ) : EReal)} ∈ 𝓝 x := by
    filter_upwards [htend x hx (C - 1)] with y hy
    by_cases hyA : y ∈ A
    · simp [hyA]
    · simpa [hyA] using (hy hyA).le
  have hle : extensionAcross A u x ≤ ((C - 1 : ℝ) : EReal) := by
    rw [extensionAcross]
    refine (uscRegularization_le_localSup _ hU).trans (iSup₂_le fun y hy => hy)
  exact hle.trans_lt (EReal.coe_lt_coe_iff.mpr (by linarith))

/-- For the pole-valued representative occurring in Step 3, upper
regularization changes no value. -/
theorem extensionAcross_eq_self_of_tendsToBotOff (hA : IsClosed A)
    (hoff : ThetaPshOff theta A u) (hbot : ∀ x ∈ A, u x = ⊥)
    (htend : TendsToBotOff A u) : extensionAcross A u = u := by
  funext x
  by_cases hx : x ∈ A
  · rw [extensionAcross_eq_bot_of_tendsToBotOff htend hx, hbot x hx]
  · exact extensionAcross_eq_of_notMem hA hoff hx

/-- Theta-PSH off `A` and local closure over `A` are sufficient for the upper
regularized function to be globally theta-PSH. -/
theorem thetaPlurisubharmonic_extensionAcross_of_localClosure (hA : IsClosed A)
    (hoff : ThetaPshOff theta A u) (hclosure : ThetaPshLocalClosure theta A u) :
    ThetaPlurisubharmonic theta (extensionAcross A u) := by
  intro e z hz
  by_cases hzA : e.val.symm z ∈ A
  · exact hclosure e z hz hzA
  · obtain ⟨W, rho, hzW, hrho, hpsh⟩ := hoff e z hz hzA
    have hW : IsOpen (W ∩ (e.val.target ∩ e.val.symm ⁻¹' Aᶜ)) :=
      hrho.1.inter (e.val.isOpen_inter_preimage_symm hA.isOpen_compl)
    refine ⟨W ∩ (e.val.target ∩ e.val.symm ⁻¹' Aᶜ), rho,
      ⟨hzW, hz, hzA⟩, hrho.mono hW inter_subset_left, ?_⟩
    intro w hw
    refine (hpsh w hw.1).congr ?_
    filter_upwards [hW.mem_nhds hw] with w' hw'
    simp only [chartFunction, extensionAcross_eq_of_notMem hA hoff hw'.2.2]

/-- The previously verified codimension-two flattening theorem supplies the
local closure package.  This is the currently available genuine special case
of the general analytic removable-singularity theorem. -/
theorem thetaPshLocalClosure_of_codimTwoFlattenings (hA : IsClosed A)
    (hflat : HasCodimTwoFlattenings (n := n) A)
    (htheta : HasSmoothLocalPotentials theta) (hoff : ThetaPshOff theta A u) :
    ThetaPshLocalClosure theta A u := by
  have hext : ThetaPlurisubharmonic theta (extensionAcross A u) :=
    thetaPlurisubharmonic_extensionAcross hA hflat htheta hoff
  intro e z hz _
  exact hext e z hz

/-- Hence codimension-two flattenings give a fully verified analytic-set
extension theorem. -/
theorem thetaPlurisubharmonic_extensionAcross_of_codimTwoFlattenings (hA : IsClosed A)
    (hflat : HasCodimTwoFlattenings (n := n) A)
    (htheta : HasSmoothLocalPotentials theta) (hoff : ThetaPshOff theta A u) :
    ThetaPlurisubharmonic theta (extensionAcross A u) :=
  thetaPlurisubharmonic_extensionAcross hA hflat htheta hoff

/-- A proper analytic subset of a connected complex manifold has empty
interior.  This supplies the non-vacuity condition in the general removable
singularity theorem. -/
theorem IsComplexAnalyticSubset.interior_eq_empty_of_ne_univ [ConnectedSpace M]
    (hA : IsComplexAnalyticSubset (n := n) A) (hproper : A ≠ univ) : interior A = ∅ := by
  rw [← not_nonempty_iff_eq_empty]
  intro hinterior
  exact hproper (hA.eq_univ_of_interior_nonempty hinterior)

/-- The exact unresolved Grauert--Remmert implication, factored down to its
local conclusion at the analytic set.  It is a proposition, not an assumed
theorem, so consumers must explicitly provide the missing analytic argument. -/
def AnalyticRemovableThetaPsh (theta : SmoothRealForm n M 2) (A : Set M)
    (u : M → EReal) : Prop :=
  IsComplexAnalyticSubset (n := n) A → A ≠ univ → ThetaPshOff theta A u →
    LocallyBoundedAboveOff A u → ThetaPshLocalClosure theta A u

/-- Applying the local Grauert--Remmert interface gives the upper-regularized
theta-PSH extension. -/
theorem thetaPlurisubharmonic_extensionAcross_of_analyticRemovable [ConnectedSpace M]
    (hremovable : AnalyticRemovableThetaPsh theta A u)
    (hanalytic : IsComplexAnalyticSubset (n := n) A) (hproper : A ≠ univ)
    (hoff : ThetaPshOff theta A u) (hbound : LocallyBoundedAboveOff A u) :
    ThetaPlurisubharmonic theta (extensionAcross A u) :=
  thetaPlurisubharmonic_extensionAcross_of_localClosure hanalytic.isClosed hoff
    (hremovable hanalytic hproper hoff hbound)

/-- This is the exact Step-3 wrapper.  Once the local Grauert--Remmert theorem
is supplied, a pole-valued branch which tends to `-∞` along its proper
analytic exceptional set is theta-PSH without any further gluing argument. -/
theorem thetaPlurisubharmonic_of_analyticRemovable [ConnectedSpace M]
    (hremovable : AnalyticRemovableThetaPsh theta A u)
    (hanalytic : IsComplexAnalyticSubset (n := n) A) (hproper : A ≠ univ)
    (hoff : ThetaPshOff theta A u) (hbound : LocallyBoundedAboveOff A u)
    (hbot : ∀ x ∈ A, u x = ⊥) (htend : TendsToBotOff A u) :
    ThetaPlurisubharmonic theta u := by
  rw [← extensionAcross_eq_self_of_tendsToBotOff hanalytic.isClosed hoff hbot htend]
  exact thetaPlurisubharmonic_extensionAcross_of_analyticRemovable hremovable hanalytic
    hproper hoff hbound

end

end Hironaka.PshAnalyticSetExtension
