import Hironaka.Resolution.HironakaActualNativeBornWeightedExponents
import Hironaka.Resolution.HironakaG1CoefficientCarrierClassData
import Hironaka.Resolution.HironakaG11PresLineStable
import Hironaka.Resolution.HironakaG1OriginalUnequalMarkCanonical

/-! The boundary-trace input for exact exponent comparison of independent native presentations. -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG1NativeBoundaryTrace
noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal ResolutionInvariantSpec
  HironakaG11PresLineState HironakaG11PresLineStable
  HironakaActualNativeBornWeightedExponents HironakaNormalCrossingsFiniteMarkedCompletion
  HironakaG1CoefficientCarrierClassData HironakaG11InvBMClass HironakaG8LocalHistory
  DivisorExponent DivisorExponentAlong GermIdealOrder FactorizationFromResolution
  HironakaG1OriginalUnequalMarkCanonical HironakaG8GapNormalizedExponent CanonicalCentres

variable {n k l : ℕ} {X : CMfd.{0} n}
  {W : Set X} {P Q : MarkedIdeal n X} {A : ℕ → ℕ}

/-- On an actual native cut point, divisibility by a smooth original boundary
member to order one is exactly local containment of the boundary in the
underlying reduced analytic set. -/
theorem native_boundary_divides_once_iff
    (hP : NativeHSState P W A) (hD : IsInvDomain k P)
    (i : Fin P.E.length) (x : X) (hx : x ∈ P.cosupp) (hxE : x ∈ P.E.get i) :
    IsDivNearAlong n P.N P.ideal (P.E.get i) 1 x ↔
      ∀ᶠ y in 𝓝 x, y ∈ P.E.get i → y ∈ W := by
  obtain ⟨_,hW,hN,hI,V,S,j,a,w,_,hPos,_,_,_,_,hAt⟩ := hP
  let J := vanishingIdeal (n := n) W
  let H := P.E.get i
  have hJ : J.IsCoherent := CartanIrreducible.cartanCoherence W hW
  have hE := hD.isWellFormed.isSNCDivisor
  obtain ⟨r,hReg⟩ := (snc_member_codimOne_geometry hE i).1.2 x hxE
  have hIH := DivisorMetric.isCoherent_of_isInvertible (isInvertible_vanishingIdeal_snc_member hE i)
  obtain ⟨Φ,_,h0,_,hTests,_⟩ := actual_native_point_reduced_stalk_dictionary
    S a w hPos W hW P hI x (hAt x hx)
  have hNear : IsDivNear n P.ideal H 1 x ↔ IsDivNear n J H 1 x := by
    rw [isDivNear_iff hI hReg, isDivNear_iff hJ hReg, idealPow_one_of_isCoherent hIH]
    exact hTests H hIH
  rw [hN, isDivNearAlong_univ_iff, hNear]
  unfold IsDivNear
  have hJhol : ∀ y F, J.mem y F → HolomorphicAt n F y := fun _ _ h => h.1
  rw [cosupport_one hJhol, univ_inter,
    BlowupExceptionalDivisor.zeroLocus_vanishingIdeal hW.isClosed]

/-- A boundary slot whose reduced trace escapes the original analytic set
has zero exponent in the entire original weighted ideal. -/
theorem native_boundary_exponent_zero_of_not_contained
    (hP : NativeHSState P W A) (hD : IsInvDomain k P)
    (i : Fin P.E.length) (x : X) (hx : x ∈ P.cosupp) (hxE : x ∈ P.E.get i)
    (hOutside : ¬ ∀ᶠ y in 𝓝 x, y ∈ P.E.get i → y ∈ W) :
    divExpAlong n P.N P.ideal (P.E.get i) x = 0 := by
  by_contra hn
  apply hOutside
  apply (native_boundary_divides_once_iff hP hD i x hx hxE).mp
  exact (isDivNearAlong_divExpAlong
    (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hP.2.2.2.1 hg) x).mono
      (Nat.one_le_iff_ne_zero.mpr hn)

/-- A boundary trace contained in the reduced analytic set but escaping the
native cut has strictly positive, strictly submark raw boundary exponent.
In this geometry a coefficient gap for the unrecoded record is impossible. -/
theorem native_boundary_submark_of_trace_gap
    (hP : NativeHSState P W A) (hD : IsInvDomain k P)
    (i : Fin P.E.length) (x : X) (hx : x ∈ P.cosupp) (hxE : x ∈ P.E.get i)
    (hIn : ∀ᶠ y in 𝓝 x, y ∈ P.E.get i → y ∈ W)
    (hOut : ¬ ∀ᶠ y in 𝓝 x, y ∈ P.E.get i → y ∈ P.cosupp) :
    (0 < divExpAlong n P.N P.ideal (P.E.get i) x ∧
      divExpAlong n P.N P.ideal (P.E.get i) x < P.d) ∧ ¬ HasCosupportGap P := by
  have hxN := P.cosupp_subset_N hx
  have hDiv (e : ℕ) := isDivNearAlong_get_iff_le hD.isWellFormed.isClosedSubmanifold_N
    hD.isWellFormed.isCoherent i hxN hxE (hD.isNonzeroAlongAt x hxN) (e := e)
  have hPos : 0 < divExpAlong n P.N P.ideal (P.E.get i) x :=
    (hDiv 1).mp ((native_boundary_divides_once_iff hP hD i x hx hxE).mpr hIn)
  refine ⟨⟨hPos,?_⟩,?_⟩
  · apply lt_of_not_ge
    intro hMark
    have hLocal : IsDivNearAlong n P.N P.ideal (P.E.get i) P.d x := (hDiv P.d).mpr hMark
    apply hOut
    exact Filter.Eventually.mono hLocal (fun _ h e => h (hP.2.2.1.symm ▸ mem_univ _) e)
  · intro hg
    apply hOut
    exact (trace_cosupp_of_gap_pos P hD hg i hxN hxE hPos).mono
      (fun _ h e => h (hP.2.2.1.symm ▸ mem_univ _) e)


/-- Exact normalized raw exponents for independent native presentations at
their original marks. The geometric hypothesis requires any locally contained
boundary trace at a cut point to lie in the actual common Hilbert–Samuel cut. -/
theorem normalized_native_boundary_exponents_of_trace
    (hn : 0 < n) (hP : NativeHSState P W A) (hQ : NativeHSState Q W A)
    (hPD : IsInvDomain k P) (hQD : IsInvDomain l Q) (hE : Q.E = P.E)
    (hTrace : ∀ (i : Fin P.E.length) (x : X), x ∈ P.cosupp → x ∈ P.E.get i →
      (∀ᶠ y in 𝓝 x, y ∈ P.E.get i → y ∈ W) →
      ∀ᶠ y in 𝓝 x, y ∈ P.E.get i → y ∈ P.cosupp) :
    ∀ H ∈ P.E, ∀ x ∈ P.cosupp, x ∈ H →
      Q.d * divExpAlong n P.N P.ideal H x = P.d * divExpAlong n Q.N Q.ideal H x := by
  have hClass : LocWPEquiv P Q := locWPEquiv_native hP hQ hE
  have hDim : SameCarrierDim P Q := SameCarrierDim.of_N_eq (hP.2.2.1.trans hQ.2.2.1.symm)
  intro H hH x hx hxH
  obtain ⟨i,rfl⟩ := List.get_of_mem hH
  by_cases hContained : ∀ᶠ y in 𝓝 x, y ∈ P.E.get i → y ∈ W
  · exact normalized_exponent_of_trace_sameCarrierDim hn P Q hPD hQD hClass hDim _
      (List.get_mem _ _) x hx hxH ((hTrace i x hx hxH hContained).mono (fun _ h _ => h))
  · let j : Fin Q.E.length := ⟨i.val, hE.symm ▸ i.isLt⟩
    have hSlot : Q.E.get j = P.E.get i := by
      simp only [List.get_eq_getElem]
      exact getElem_congr hE rfl j.isLt
    have hxQ : x ∈ Q.cosupp := hClass.cosupp_eq_base ▸ hx
    have hPZero := native_boundary_exponent_zero_of_not_contained hP hPD i x hx hxH hContained
    have hQZero := native_boundary_exponent_zero_of_not_contained hQ hQD j x hxQ
      (hSlot.symm ▸ hxH) (by rwa [hSlot])
    rw [hSlot] at hQZero
    rw [hPZero,hQZero,Nat.mul_zero,Nat.mul_zero]

/-- Independent native marks on the same actual history have equivalent
canonicality whenever each contained original boundary trace lies in the cut. -/
theorem native_canonical_iff_of_boundary_trace
    {Y : CMfd.{0} n} (hn : 0 < n)
    (hP : NativeHSState P W A) (hQ : NativeHSState Q W A)
    (hPD : IsInvDomain k P) (hQD : IsInvDomain k Q) (hE : Q.E = P.E)
    (hTrace : ∀ (i : Fin P.E.length) (x : X), x ∈ P.cosupp → x ∈ P.E.get i →
      (∀ᶠ y in 𝓝 x, y ∈ P.E.get i → y ∈ W) →
      ∀ᶠ y in 𝓝 x, y ∈ P.E.get i → y ∈ P.cosupp)
    (T : BlowupTower X Y) :
    IsCanonical P ((invFamily hn k).inv P) T ↔ IsCanonical Q ((invFamily hn k).inv Q) T :=
  invFamily_isCanonical_iff_of_local hn P Q hPD hQD (locWPEquiv_native hP hQ hE)
    (SameCarrierDim.of_N_eq (hP.2.2.1.trans hQ.2.2.1.symm))
    (normalized_native_boundary_exponents_of_trace hn hP hQ hPD hQD hE hTrace) T

#print axioms native_boundary_divides_once_iff
#print axioms native_boundary_submark_of_trace_gap
#print axioms normalized_native_boundary_exponents_of_trace
#print axioms native_canonical_iff_of_boundary_trace

end
end Hironaka.HironakaG1NativeBoundaryTrace
