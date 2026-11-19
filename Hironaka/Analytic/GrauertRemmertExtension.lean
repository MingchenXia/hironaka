import Hironaka.Analytic.PshAnalyticSetExtension

set_option autoImplicit false

/-!
# Grauert--Remmert reduction to the hypersurface stratum

This module isolates the remaining analytic content of the removable-singularity
step in Demailly regularization.  It proves, without an additional analytic
axiom, that a local extension theorem on the regular hypersurface stratum,
together with the verified codimension-two extension theorem, gives the full
analytic-set local closure required by `AnalyticRemovableThetaPsh`.

The key bookkeeping fact is exact: if `Z ⊆ A`, then deleting the values on `Z`
and upper-regularizing after already upper-regularizing across `A` changes
nothing.  Thus the codimension-two extension applies to the same candidate,
rather than to a silently different representative.

The only remaining unproved mathematical input is therefore the local
Grauert--Remmert theorem at the codimension-one regular stratum of a proper
analytic set.  It is exposed below as the explicit `ThetaPshLocalClosureOn`
hypothesis; no global closure conclusion is stored as a field or assumed.
-/

open Set Filter
open scoped Topology

namespace Hironaka.GrauertRemmertExtension


open ThetaPshCodimTwoExtension
open PshAnalyticSetExtension

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

variable {A Z : Set M} {theta : SmoothRealForm n M 2} {u : M → EReal}

/-- The chartwise local theta-PSH conclusion on a designated stratum.  Here
`v` is already the prescribed upper-regularized candidate; this predicate
contains no assertion at points outside `S`. -/
def ThetaPshLocalClosureOn (theta : SmoothRealForm n M 2) (v : M → EReal)
    (S : Set M) : Prop :=
  ∀ e z, z ∈ e.val.target → e.val.symm z ∈ S →
    ∃ W rho, z ∈ W ∧ IsSmoothLocalPotential theta e W rho ∧
      PlurisubharmonicOn (fun y => chartFunction v e y + (rho y : EReal)) W

/-- Removing a smaller exceptional set after regularizing across a larger one
has no effect.  The forward inequality uses the upper-semicontinuity of the
first regularization; the reverse inequality is monotonicity of upper
regularization. -/
theorem extensionAcross_nested_eq (hZA : Z ⊆ A) :
    extensionAcross Z (extensionAcross A u) = extensionAcross A u := by
  classical
  apply le_antisymm
  · apply uscRegularization_le (upperSemicontinuous_uscRegularization _)
    intro x
    by_cases hxZ : x ∈ Z
    · simp [hxZ]
    · simp [extensionAcross, hxZ]
  · apply uscRegularization_mono
    intro x
    by_cases hxA : x ∈ A
    · by_cases hxZ : x ∈ Z
      · simp [hxA, hxZ]
      · simp [extensionAcross, hxA, hxZ]
    · have hxZ : x ∉ Z := fun hxZ => hxA (hZA hxZ)
      simp only [extensionAcross, hxA, hxZ, if_false]
      simpa [extensionAcross, hxA, hxZ] using
        (le_uscRegularization (fun y => if y ∈ A then (⊥ : EReal) else u y) x)

/-- Once the prescribed candidate has the local theta-PSH conclusion on the
part of `A` outside `Z`, it is theta-PSH off `Z`.  Away from `A` this follows
from the original off-set hypothesis and exact equality of the first upper
regularization with `u`. -/
theorem thetaPshOff_extensionAcross_of_localClosureOn (hA : IsClosed A)
    (hoff : ThetaPshOff theta A u)
    (hregular : ThetaPshLocalClosureOn theta (extensionAcross A u) (A \ Z)) :
    ThetaPshOff theta Z (extensionAcross A u) := by
  intro e z hz hzZ
  by_cases hzA : e.val.symm z ∈ A
  · exact hregular e z hz ⟨hzA, hzZ⟩
  · obtain ⟨W, rho, hzW, hrho, hpsh⟩ := hoff e z hz hzA
    have hW : IsOpen (W ∩ (e.val.target ∩ e.val.symm ⁻¹' Aᶜ)) :=
      hrho.1.inter (e.val.isOpen_inter_preimage_symm hA.isOpen_compl)
    refine ⟨W ∩ (e.val.target ∩ e.val.symm ⁻¹' Aᶜ), rho,
      ⟨hzW, hz, hzA⟩, hrho.mono hW inter_subset_left, ?_⟩
    intro w hw
    refine (hpsh w hw.1).congr ?_
    filter_upwards [hW.mem_nhds hw] with w' hw'
    simp only [chartFunction, extensionAcross_eq_of_notMem hA hoff hw'.2.2]

/-- **Codimension-two core reduction.**  Suppose `Z ⊆ A` has the verified
codimension-two flattenings and the candidate is locally theta-PSH at every
point of `A \ Z`.  Then it has the local closure conclusion at every point of
`A`.  This is the induction step which leaves only the regular hypersurface
stratum to the analytic Grauert--Remmert argument. -/
theorem thetaPshLocalClosure_of_codimTwoCore (hA : IsClosed A) (hZ : IsClosed Z)
    (hZA : Z ⊆ A) (hflat : HasCodimTwoFlattenings (n := n) Z)
    (htheta : HasSmoothLocalPotentials theta) (hoff : ThetaPshOff theta A u)
    (hregular : ThetaPshLocalClosureOn theta (extensionAcross A u) (A \ Z)) :
    ThetaPshLocalClosure theta A u := by
  have hoffZ : ThetaPshOff theta Z (extensionAcross A u) :=
    thetaPshOff_extensionAcross_of_localClosureOn hA hoff hregular
  have hext : ThetaPlurisubharmonic theta
      (extensionAcross Z (extensionAcross A u)) :=
    thetaPlurisubharmonic_extensionAcross hZ hflat htheta hoffZ
  rw [extensionAcross_nested_eq hZA] at hext
  intro e z hz _
  exact hext e z hz

/-- The completely verified codimension-two special case of the analytic
removability interface. -/
theorem analyticRemovableThetaPsh_of_codimTwoFlattenings
    (htheta : HasSmoothLocalPotentials theta)
    (hflat : HasCodimTwoFlattenings (n := n) A) :
    AnalyticRemovableThetaPsh theta A u := by
  intro hanalytic _ hoff _
  exact thetaPshLocalClosure_of_codimTwoFlattenings hanalytic.isClosed hflat htheta hoff

/-- A stratified Grauert--Remmert input has exactly one analytic obligation:
for a closed codimension-two core `Z ⊆ A`, establish local closure on the
complementary stratum `A \ Z`.  The conclusion is the existing
`AnalyticRemovableThetaPsh` interface, so consumers do not need any further
regularization or gluing theorem. -/
theorem analyticRemovableThetaPsh_of_codimTwoCore
    (htheta : HasSmoothLocalPotentials theta)
    (hcore : ∀ (_hanalytic : IsComplexAnalyticSubset (n := n) A) (_hproper : A ≠ univ)
      (_hoff : ThetaPshOff theta A u) (_hbound : LocallyBoundedAboveOff A u),
      ∃ Z : Set M, IsClosed Z ∧ Z ⊆ A ∧ HasCodimTwoFlattenings (n := n) Z ∧
        ThetaPshLocalClosureOn theta (extensionAcross A u) (A \ Z)) :
    AnalyticRemovableThetaPsh theta A u := by
  intro hanalytic hproper hoff hbound
  obtain ⟨Z, hZ, hZA, hflat, hregular⟩ := hcore hanalytic hproper hoff hbound
  exact thetaPshLocalClosure_of_codimTwoCore hanalytic.isClosed hZ hZA hflat htheta hoff hregular

end

end Hironaka.GrauertRemmertExtension
