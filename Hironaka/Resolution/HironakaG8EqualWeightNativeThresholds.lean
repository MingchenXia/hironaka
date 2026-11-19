import Hironaka.Resolution.HironakaActualCoherentWeightedCoefficientMarked
import Hironaka.Resolution.HironakaG8NativeResidualWeightCriterion
import Hironaka.Resolution.HironakaG8P1NormalizedOrder

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace

namespace Hironaka.HironakaG8EqualWeightNativeThresholds
noncomputable section

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers GermIdealOrder IdealWeightPowers OrderTaylor OrderMultiplicativity CompanionReduction
  MarkedIdeals MarkedIdeals.MarkedIdeal HironakaActualCoherentWeightedCoefficientMarked
  HironakaActualWeightedCoefficientCompression RelativePrincipalizationSpan
  HironakaG8P1NormalizedOrder NonmonomialOrderLocal HironakaG8LocalHistory HironakaG11InvBMClass
  HironakaSharpOriginalProductTraceOrder ResolutionInvariantSpec ResolutionDriver CanonicalCentres

private theorem vanishes_power_on_whole {n : ℕ} {X : CMfd.{0} n}
    (x : X) (f : X → ℂ) (q : ℕ) (h : VanishesToOrderOn n univ x q f) :
    ∀ e, VanishesToOrderOn n univ x (q*e) (fun y => f y ^ e)
  | 0 => by simpa only [Nat.mul_zero, pow_zero] using
      vanishesToOrderOn_zero (n := n) (N := (univ : Set X)) (x := x) (holomorphicAt_const 1)
  | e+1 => by simpa only [Nat.mul_succ, pow_succ] using (vanishes_power_on_whole x f q h e).mul h

/-- The powers of genuine equal-weight coefficients preserve every scaled
ordinary threshold, including points outside the designated active locus. -/
theorem equal_weight_native_thresholds
    {n : ℕ} {X : CMfd.{0} n} {ι : Type} [Fintype ι]
    (w : ι → ℕ) (o : ℕ) (ho : 0 < o) (hw : ∀ i, w i = o)
    (f : ι → X → ℂ) (hf : ∀ x i, HolomorphicAt n (f i) x)
    (q : ℕ) :
    cosupport n univ (weightedFunctionIdeal w f) (q * (weightedCommonMark w / o)) =
      cosupport n univ (finiteFunctionIdeal f) q := by
  let e := weightedCommonMark w / o
  have he (i : ι) : 1 ≤ e := by
    have hm := compressionExponent_pos w (fun j => hw j ▸ ho) i
    rwa [hw] at hm
  have hFamily : weightedFunctionIdeal (n := n) w f =
      finiteFunctionIdeal (fun i y => f i y ^ e) := by
    unfold weightedFunctionIdeal
    have h : (fun i y => f i y ^ (weightedCommonMark w / w i)) =
        (fun i y => f i y ^ e) := by funext i y; rw [hw]
    rw [h]
  ext x
  rw [hFamily, mem_cosupport_finiteFunctionIdeal_iff _ x _ (fun i => holomorphicAt_pow_of (hf x i) _),
    mem_cosupport_finiteFunctionIdeal_iff _ x _ (hf x)]
  apply forall_congr'
  intro i
  exact ⟨fun h => by
    have hPow := mem_idealPow_of_vanishesToOrderOn_univ h
    rw [Nat.mul_comm q e] at hPow
    have hRoot := mem_idealPow_of_pow_mem (hf x i) (he i) hPow
    exact ⟨f i,hRoot,Filter.Eventually.of_forall fun _ _ => rfl⟩,
    fun h => vanishes_power_on_whole x (f i) q h e⟩

/-- On the native active locus, local weak projection equivalence to an
alternative reference requires its own ordinary top order to be exactly
its mark. Whole-power normalization preserves this obstruction. -/
theorem not_locWPEquiv_of_wrong_active_reference_order
    {n : ℕ} {X : CMfd.{0} n} (Q R : MarkedIdeal n X)
    (hq : IsInvDomain n Q) (hr : IsInvDomain n R) (hDim : SameCarrierDim Q R)
    {x : X} (hx : x ∈ Q.cosupp)
    (hOrderQ : ordinaryTraceOrder Q.N Q.ideal x = Q.d)
    (hWrong : ordinaryTraceOrder R.N R.ideal x ≠ R.d) :
    ¬ LocWPEquiv Q R := by
  intro h
  have hEq := normalized_order_eq_of_locWPEquiv h hq hr hDim hx
  rw [hOrderQ, Nat.mul_comm R.d Q.d] at hEq
  exact hWrong ((Nat.eq_of_mul_eq_mul_left (by have := hq.one_le_d; omega) hEq).symm)

/-- A weak-projection equivalent reference for a native active record at
ordinary maximal order has an ordinary global cap at its own mark. -/
theorem reference_cap_of_native_active_order
    {n : ℕ} {X : CMfd.{0} n} (Q R : MarkedIdeal n X)
    (hq : IsInvDomain n Q) (hr : IsInvDomain n R) (hDim : SameCarrierDim Q R)
    (hClass : LocWPEquiv Q R)
    (hActive : ∀ x ∈ Q.cosupp, ordinaryTraceOrder Q.N Q.ideal x = Q.d) :
    HomogenizedIdealAlong.IsMaximalOrderAlong R.N R.ideal R.d := by
  intro x hx
  have hxR : x ∈ R.cosupp := cosupport_anti (Nat.le_succ R.d) hx
  have hxQ : x ∈ Q.cosupp := hClass.cosupp_eq_base.symm ▸ hxR
  have hEq := normalized_order_eq_of_locWPEquiv hClass hq hr hDim hxQ
  rw [hActive x hxQ, Nat.mul_comm R.d Q.d] at hEq
  have hOrd := Nat.eq_of_mul_eq_mul_left (by have := hq.one_le_d; omega) hEq
  have hxOrder := (ordinaryTraceOrder_cosupport_iff hr.isWellFormed.isClosedSubmanifold_N
    hr.isWellFormed.isCoherent hr.isNonzeroAlongAt hx.1 _).mp hx
  omega

/-- An independently constructed top-mark reference may carry the low
raw residual even when the actual weighted native ideal differs from it.
The native simultaneous maxima first supply canonicality for the
reference through the class and scaled exponent conditions. -/
theorem native_simultaneous_canonical_via_residual_reference
    {n : ℕ} {X Y : CMfd.{0} (n+1)} {I : Type}
    (U : I → Opens X) (Q : ∀ i, MarkedIdeal (n+1) (CMfd.of (n := n+1) (U i)))
    (hq : ∀ i, IsInvDomain (n+1) (Q i)) (e : I → ℕ) (he : ∀ i, 1 ≤ e i)
    (T : BlowupTower X Y)
    (hSync : HironakaG8NativeSimultaneousCentre.NativeSimultaneousStages
      (canonicalInvariant (n+1)) U (fun i => HironakaActualPowerBoundaryExponents.powerMarked (Q i) (e i)) T)
    (i : I) (P R : MarkedIdeal (n+1) (CMfd.of (n := n+1) (U i)))
    (hp : IsInvDomain (n+1) P) (hr : IsInvDomain (n+1) R)
    (hPN : P.N = univ) (hRN : R.N = univ) (hQN : (Q i).N = univ)
    (hE : P.E = R.E) (hd : P.d ≤ R.d) (hResidual : nmPart P = R.ideal)
    (hClass : LocWPEquiv (Q i) R)
    (hInitial : ∀ H ∈ (Q i).E, ∀ x ∈ (Q i).cosupp, x ∈ H →
      R.d * DivisorExponentAlong.divExpAlong (n+1) (Q i).N (Q i).ideal H x =
        (Q i).d * DivisorExponentAlong.divExpAlong (n+1) R.N R.ideal H x)
    (hActive : ∀ x ∈ (Q i).cosupp, ordinaryTraceOrder (Q i).N (Q i).ideal x = (Q i).d) :
    IsCanonical P ((canonicalInvariant (n+1)).inv P) (BlowupTowerTransforms.restrict (U i) T) := by
  have hDim := SameCarrierDim.of_N_eq (X := CMfd.of (n := n+1) (U i)) (hQN.trans hRN.symm)
  let S := BlowupTowerTransforms.restrict (U i) T
  have hQCan : IsCanonical (Q i) ((canonicalInvariant (n+1)).inv (Q i)) S := by
    rw [HironakaSmoothSubmersionOriginalAmbientCanonical.canonicalInvariant_eq_invFamily (Nat.succ_pos n)]
    exact HironakaG8NativePrefixOriginalCanonical.simultaneous_powered_prefix_raw_canonical
      (Nat.succ_pos n) U Q hq e he T hSync i
  have hRCan := (HironakaG1OriginalUnequalMarkCanonical.canonicalInvariant_isCanonical_iff_of_local
    (Q i) R (hq i) hr hClass hDim hInitial S).mp hQCan
  have hNo : HironakaG8PrincipalRetainedEpochFinite.HasNoBoundaryFactor R := by
    have hWitness := (NonmonomialTransformAlong.parts_hypotheses (Nat.succ_pos n)
      P hp.isWellFormed hp.isNonzeroAlongAt).2.2.2.2.1
    change ∀ x ∈ P.N, ∀ j : Fin P.E.length, x ∈ P.E.get j →
      ∃ a, (nmPart P).mem x a ∧
        ¬ IsInSpanOnAt (n := n+1) P.N ((vanishingIdeal (n := n+1) (P.E.get j)).mem x) x a at hWitness
    rw [hPN.trans hRN.symm,hE,hResidual] at hWitness
    exact hWitness
  have hPart : nmPart P = nmPart R := by
    have hw := hr.isWellFormed
    have h : nmPart R = RestrictedIdealExtension.restrictOn _ R.N R.ideal :=
      HironakaSharpActualChronologicalResidualDictionary.nonmonomialPartAlong_eq_restrictOn_of_no_member_factor
        hw.isClosedSubmanifold_N hw.isSNCDivisor hw.isTransverse hw.isCoherent hNo
    rw [hRN,BlowupTowerTransforms.restrictOn_univ hw.isCoherent] at h
    exact hResidual.trans h.symm
  have hLe : P.ideal.Le R.ideal := hResidual ▸ NonmonomialTransformAlong.le_nonmonomialPartAlong_self
    hp.isWellFormed.isCoherent
  have hUpper := reference_cap_of_native_active_order (Q i) R (hq i) hr hDim hClass hActive
  have hCap (x : CMfd.of (n := n+1) (U i)) : nmOrd R x ≤ R.d := by
    apply nmOrd_le_of_notMem
    rw [HironakaG8PrincipalRetainedEpochFinite.ordGe_eq_cosupport_of_hasNoBoundaryFactor
      R hr.isWellFormed hNo]
    exact hUpper x
  exact HironakaG8SharedResidualInitialFactorFree.shared_residual_phase_isCanonical_of_initial_factor_free
    P R hp hr hPN hRN hE hLe hd hPart hNo hCap S hRCan

end
end Hironaka.HironakaG8EqualWeightNativeThresholds
