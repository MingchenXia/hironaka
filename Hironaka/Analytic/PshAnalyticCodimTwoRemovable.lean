import Hironaka.Analytic.GrauertRemmertExtension
import Hironaka.Analytic.RegularAtDimChart

set_option autoImplicit false

/-!
# Correct analytic codimension-two core reduction

The older `HasCodimTwoFlattenings` interface is deliberately a special case:
it asks that the *whole* exceptional set be locally contained in a smooth
coordinate plane.  That is false for a singular analytic codimension-two
set, for example a cuspidal curve in a threefold.  This file records the
valid replacement bookkeeping.

At a regular point whose complex dimension is at most `n - 2`, the existing
`RegularAtDim` witness does give a codimension-two flattening.  For a general
analytic core, however, one must use its own removable-singularity statement
after extending through the complementary stratum.  The theorems below prove
this recursion exactly; they do not assert a nonexistent flattening of a
singular core or an unproved analytic stratification theorem.
-/

open Set Filter
open scoped Topology

namespace Hironaka.PshAnalyticCodimTwoRemovable


open ThetaPshCodimTwoExtension
open PshAnalyticSetExtension
open GrauertRemmertExtension
open BlowupFlatCoordinates

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

variable {A Z : Set M} {theta : SmoothRealForm n M 2} {u : M → EReal}

/-- The pointwise form of the already verified codimension-two flattening
condition.  Unlike `HasCodimTwoFlattenings`, it makes no assertion at nearby
singular points. -/
def HasCodimTwoFlatteningAt (K : Set M) (p : M) : Prop :=
  ∃ k : ℕ, k + 2 ≤ n ∧
    ∃ Phi : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) p p),
      Phi.source ⊆ (chartAt (ComplexModel n) p).target ∧
      ∀ y ∈ BlowupFlatCoordinates.flatDomain Phi, y ∈ K →
        Phi.toFun (chartAt (ComplexModel n) p y) ∈ complexCoordinatePlane n k

omit [IsComplexManifold n M] in
/-- A regular analytic point of complex codimension at least two supplies the
pointwise flattening required by the codimension-two local argument. -/
theorem hasCodimTwoFlatteningAt_of_regularAtDim {x : M} {k : ℕ}
    (hx : RegularAtDim (n := n) A x k) (hk : k + 2 ≤ n) :
    HasCodimTwoFlatteningAt (n := n) A x := by
  obtain ⟨-, -, Phi, hsource, -, hflat⟩ := hx
  refine ⟨k, hk, Phi, hsource, ?_⟩
  intro y hyflat hyA
  exact (hflat hyflat.1 hyflat.2).mp hyA

def regularCodimTwoLocus (A : Set M) : Set M :=
  {x | ∃ k : ℕ, k + 2 ≤ n ∧ RegularAtDim (n := n) A x k}

omit [IsComplexManifold n M] in
/-- Membership in the regular codimension-two locus recovers its pointwise
flattening witness. -/
theorem hasCodimTwoFlatteningAt_of_mem_regularCodimTwoLocus {x : M}
    (hx : x ∈ regularCodimTwoLocus (n := n) A) :
    HasCodimTwoFlatteningAt (n := n) A x := by
  obtain ⟨k, hk, hreg⟩ := hx
  exact hasCodimTwoFlatteningAt_of_regularAtDim hreg hk

omit [IsComplexManifold n M] in
/-- A pointwise flatness witness can be assembled to the old global special
case only when it is available at *every* point.  This makes the precise
strength of the old interface explicit. -/
theorem hasCodimTwoFlattenings_of_pointwise
    (hflat : ∀ p ∈ A, HasCodimTwoFlatteningAt (n := n) A p) :
    HasCodimTwoFlattenings (n := n) A := by
  intro p hp
  exact hflat p hp

omit [TopologicalSpace M] in
/-- A proper analytic core is proper whenever it is contained in a proper
ambient analytic exceptional set. -/
theorem ne_univ_of_subset_of_ne_univ (hZA : Z ⊆ A) (hA : A ≠ univ) : Z ≠ univ := by
  intro hZ
  apply hA
  apply eq_univ_of_forall
  intro x
  apply hZA
  rw [hZ]
  exact mem_univ x

/-- **General analytic-core induction.**  Let `Z ⊆ A` be an analytic core.
Suppose the first regularized candidate is locally theta-PSH along `A \ Z`.
If the same candidate satisfies the ordinary analytic removability interface
over `Z`, then it is locally theta-PSH at every point of `A`.

This is the valid replacement for putting `HasCodimTwoFlattenings Z` in the
same statement: a singular codimension-two core can instead be discharged by
another analytic-core induction step. -/
theorem thetaPshLocalClosure_of_analyticCore
    (hA : IsClosed A) (hZanalytic : IsComplexAnalyticSubset (n := n) Z)
    (hAproper : A ≠ univ) (hZA : Z ⊆ A)
    (hcore : AnalyticRemovableThetaPsh theta Z (extensionAcross A u))
    (hoff : ThetaPshOff theta A u)
    (hboundCore : LocallyBoundedAboveOff Z (extensionAcross A u))
    (hregular : ThetaPshLocalClosureOn theta (extensionAcross A u) (A \ Z)) :
    ThetaPshLocalClosure theta A u := by
  have hoffZ : ThetaPshOff theta Z (extensionAcross A u) :=
    thetaPshOff_extensionAcross_of_localClosureOn hA hoff hregular
  have hZproper : Z ≠ univ := ne_univ_of_subset_of_ne_univ hZA hAproper
  have hclosureZ : ThetaPshLocalClosure theta Z (extensionAcross A u) :=
    hcore hZanalytic hZproper hoffZ hboundCore
  have hext : ThetaPlurisubharmonic theta
      (extensionAcross Z (extensionAcross A u)) :=
    thetaPlurisubharmonic_extensionAcross_of_localClosure hZanalytic.isClosed hoffZ hclosureZ
  rw [extensionAcross_nested_eq hZA] at hext
  intro e z hz _
  exact hext e z hz

/-- A stratification step which is valid for an arbitrary singular analytic
core.  The core is handled by its own removability interface for the already
regularized candidate, rather than by the false assertion that it lies in a
smooth codimension-two plane. -/
theorem analyticRemovableThetaPsh_of_analyticCore
    (hcore : ∀ (_hanalytic : IsComplexAnalyticSubset (n := n) A) (_hproper : A ≠ univ)
      (_hoff : ThetaPshOff theta A u) (_hbound : LocallyBoundedAboveOff A u),
      ∃ Z : Set M, IsComplexAnalyticSubset (n := n) Z ∧ Z ⊆ A ∧
        AnalyticRemovableThetaPsh theta Z (extensionAcross A u) ∧
        LocallyBoundedAboveOff Z (extensionAcross A u) ∧
        ThetaPshLocalClosureOn theta (extensionAcross A u) (A \ Z)) :
    AnalyticRemovableThetaPsh theta A u := by
  intro hanalytic hproper hoff hbound
  obtain ⟨Z, hZanalytic, hZA, hZremovable, hZbound, hregular⟩ :=
    hcore hanalytic hproper hoff hbound
  exact thetaPshLocalClosure_of_analyticCore hanalytic.isClosed hZanalytic hproper hZA
    hZremovable hoff hZbound hregular

end

end Hironaka.PshAnalyticCodimTwoRemovable
