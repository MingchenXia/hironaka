import Hironaka.Resolution.HironakaG8NativeSharedResidualCanonical
import Hironaka.Resolution.HironakaG8NativeRelativeClearing
import Hironaka.Resolution.HironakaActualHistoricalNativeOrdinaryOrder
import Hironaka.Resolution.HironakaActualNativeBornWeightedExponents

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace

namespace Hironaka.HironakaG8NativeResidualWeightCriterion
noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences HolGerm
  GermIdealOrder BlowupTowers HironakaActualCauchyMonomialDivision MarkedIdeals MarkedIdeals.MarkedIdeal
  HironakaSmoothSubmersionGermIdealColon HironakaActualWeightedCoefficientCompression
  HironakaActualHistoricalNativeOrdinaryOrder HironakaActualHistoricalNativeStageStep
  HironakaActualFixedInheritedSelector HironakaRelativeNormalMonomialBasis
  HironakaActualNativeBornWeightedExponents HironakaSharpOriginalProductTraceOrder
  HomogenizedIdealAlong NonmonomialOrderLocal ResolutionDriver ResolutionInvariantSpec CanonicalCentres

/-- Weight compression preserves the generated coherent stalk precisely when
each unpowered generator is already in the compressed ideal. -/
theorem weightedCompression_eq_span_iff
    {ι R : Type*} [Fintype ι] [CommRing R]
    (w : ι → ℕ) (hw : ∀ i, 0 < w i) (g : ι → R) :
    weightedCompression w g = Ideal.span (range g) ↔
      ∀ i, g i ∈ weightedCompression w g := by
  constructor
  · intro h i
    rw [h]
    exact Ideal.subset_span (mem_range_self i)
  · intro h
    apply le_antisymm
    · apply Ideal.span_le.mpr
      rintro f ⟨i, rfl⟩
      obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt (compressionExponent_pos w hw i))
      change g i ^ (weightedCommonMark w / w i) ∈ Ideal.span (range g)
      rw [hm, pow_succ]
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span (mem_range_self i))
    · exact Ideal.span_le.mpr (by rintro f ⟨i, rfl⟩; exact h i)

/-- Actual all-point native data identify the cap of a proposed shared
residual whenever the raw coherent ideal identity is known. -/
theorem native_point_presentations_residual_cap
    {n k : ℕ} {X : CMfd.{0} n} {V : Finset (Fin n →₀ ℕ)}
    (S : ActualFixedInheritedSelector V) (hv : V.Nonempty)
    (a : Fin k ≃ V) (w : Fin k → CoordinateWord n)
    (hw : ∀ i, wordExponent (w i) = (a i).val)
    (W : Set X) (P Q : MarkedIdeal n X)
    (hp : P.N = univ) (hq : Q.N = univ) (hQI : Q.ideal.IsCoherent)
    (hMark : Q.d = weightedCommonMark (fun v : V => normalExponentDegree v.val))
    (hAt : ∀ x ∈ Q.cosupp, ActualHistoricalNativePointPresentation S a w W Q x)
    (hResidual : nmPart P = Q.ideal) : ∀ x, nmOrd P x ≤ Q.d := by
  have hCap := actual_native_current_maximal_order S hv a w hw W Q hq hQI hMark hAt
  intro x
  apply nmOrd_le_of_notMem
  change x ∉ cosupport n P.N (nmPart P) (Q.d+1)
  rw [hResidual,hp,← hq]
  exact hCap x

/-- The literal single-point native compression of the reduced original
ideal can agree with that reduced ideal only when the adapted weighted
stalk is radical, and this criterion is sufficient at the same point. -/
theorem native_point_reduced_ideal_eq_iff_radical
    {n k : ℕ} {X : CMfd.{0} n} {V : Finset (Fin n →₀ ℕ)}
    (S : ActualFixedInheritedSelector V) (a : Fin k ≃ V) (w : Fin k → CoordinateWord n)
    (hw : ∀ v : V, 0 < normalExponentDegree v.val)
    (W : Set X) (hW : IsComplexAnalyticSubset (n := n) W)
    (Q : MarkedIdeal n X) (hQI : Q.ideal.IsCoherent) (x : X)
    (hAt : ActualHistoricalNativePointPresentation S a w W Q x) :
    ∃ (Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel n) x x))
      (h0 : Φ.toFun (chartAt (ComplexModel n) x x) = 0),
      ((∀ f, Q.ideal.mem x f ↔ (vanishingIdeal (n := n) W).mem x f) ↔
        (adaptedIdeal Q.ideal x Φ h0).IsRadical) := by
  obtain ⟨Φ, _, h0, hRad, _, _⟩ :=
    actual_native_point_reduced_stalk_dictionary S a w hw W hW Q hQI x hAt
  refine ⟨Φ, h0, ?_⟩
  let J := vanishingIdeal (n := n) W
  have hJ := CartanIrreducible.cartanCoherence W hW
  constructor
  · intro h
    have hEq : adaptedIdeal Q.ideal x Φ h0 = adaptedIdeal J x Φ h0 := by
      unfold adaptedIdeal
      apply congrArg Ideal.span
      ext g
      constructor
      · rintro ⟨f,hf,hmem,rfl⟩
        exact ⟨f,hf,(h f).mp hmem,rfl⟩
      · rintro ⟨f,hf,hmem,rfl⟩
        exact ⟨f,hf,(h f).mpr hmem,rfl⟩
    rw [hEq]
    exact adapted_vanishingIdeal_isRadical W hJ x Φ h0
  · intro h f
    have hEq := h.radical.symm.trans hRad
    constructor
    · intro hf
      have hhol := RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hQI hf
      apply (mem_adaptedIdeal_iff J hJ x Φ h0 f hhol).mp
      rw [← hEq]
      exact (mem_adaptedIdeal_iff Q.ideal hQI x Φ h0 f hhol).mpr hf
    · intro hf
      have hhol := RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hJ hf
      apply (mem_adaptedIdeal_iff Q.ideal hQI x Φ h0 f hhol).mp
      rw [hEq]
      exact (mem_adaptedIdeal_iff J hJ x Φ h0 f hhol).mpr hf

/-- On an actual adopted native window of mark greater than one, the
native state itself supplies the retained order cap. Only the coherent
residual ideal identity and low record geometry are input. -/
theorem adopted_native_window_residual_canonical
    {n : ℕ} {X Y : CMfd.{0} (n+1)} {I : Type}
    {W D : Set X} {E : List (Set X)} {H : ℕ → ℕ}
    (A : HironakaG8NativeRelativeClearing.NativeWindows X I W E H D)
    (T : BlowupTowers.BlowupTower X Y)
    (hSync : HironakaG8NativeSimultaneousCentre.NativeSimultaneousStages
      (CanonicalCentres.canonicalInvariant (n+1)) A.openSet A.powered T)
    (i : I) (P : MarkedIdeal (n+1) (CMfd.of (n := n+1) (A.openSet i)))
    (hp : ResolutionInvariantSpec.IsInvDomain (n+1) P) (hPN : P.N = univ)
    (hE : P.E = (A.record i).E) (hResidual : nmPart P = (A.record i).ideal)
    (hd : P.d ≤ (A.record i).d) (hHigh : 1 < (A.record i).d) :
    IsCanonical P ((CanonicalCentres.canonicalInvariant (n+1)).inv P)
      (BlowupTowerTransforms.restrict (A.openSet i) T) := by
  obtain ⟨_, _, hN, hI, V, S, k, a, w, hw, _, _, hMark, _, _, hAt⟩ := A.native i
  have hv : V.Nonempty := by
    by_contra hNo
    have hEmpty := Finset.not_nonempty_iff_eq_empty.mp hNo
    have hOne : (A.record i).d = 1 := by
      rw [hMark]
      subst V
      simp [weightedCommonMark]
    omega
  have hCap := native_point_presentations_residual_cap S hv a w hw _ P (A.record i)
    hPN hN hI hMark hAt hResidual
  exact HironakaG8NativeSharedResidualCanonical.native_simultaneous_residual_record_canonical
    A.openSet A.record A.domain A.exponent A.positive T hSync i P hp hPN hN hE hResidual hd hCap

end
end Hironaka.HironakaG8NativeResidualWeightCriterion
