import Hironaka.Resolution.HironakaG8NativeGermWindowAgreement
import Hironaka.Resolution.HironakaG8OddCuspHistoricalNative
import Hironaka.Resolution.HironakaG8CuspPrefixSupportCompression

/-! Exact local certification for identifying a historical cusp record with
its displayed weighted polynomial record. -/
set_option autoImplicit false
open Set TopologicalSpace
open scoped MonomialOrder
namespace Hironaka.HironakaG8OddCuspNativeWindowAgreement
noncomputable section

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves BlowupTowers
  ResolutionInvariantSpec MarkedIdeals MarkedIdealBiholomorphism InvDomainTowerAlong
  HironakaG11PresLineState HironakaSmoothSubmersionGermIdealColon
  HironakaActualFormalInitialDiagram HironakaActualNormalZeroAnalyticSaturation
  HironakaActualCoefficientPresentationCentrePower HironakaRelativeNormalMonomialBasis
  HironakaRelativeNormalIdeal HironakaActualWeightedCoefficientCompression
  HironakaG8NativeGermWindowAgreement HironakaG8NativeCuspDiagram HironakaG8SameHSCuspContact
  HironakaG8CuspPrefixSupportCompression HironakaActualHistoricalNormalizedWeakPresentation
  HironakaActualFixedInheritedSelector HironakaActualCauchyMonomialDivision

/-- For the literal standard-basis labels, the actual point-history laws and
the adapted polynomial stalk suffice for equality on a
smaller open and transport of the full historical native state there. -/
theorem exists_aligned_cusp_native_window_agreement
    {X : CMfd.{0} 3} (p : ℕ) (hp : 2 < p)
    {W : Set X} {H : ℕ → ℕ} {Q P : MarkedIdeal 3 X}
    (hQ : NativeHSState Q W H) (hP : P.ideal.IsCoherent)
    (hN : Q.N = P.N) (hE : Q.E = P.E) (hPMark : P.d = 2)
    (x : X) (Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel 3) x x))
    (hΦ0 : Φ.toFun (chartAt (ComplexModel 3) x x) = 0)
    (U : Opens X) (hx : x ∈ U)
    (Γ : actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal 3 (embeddedCuspIdeal p)) →
      HolGerm (ComplexModel 3))
    (hMark : Q.d = weightedCommonMark (fun a : actualInitialVertices MonomialOrder.degLex
      (analyticZeroTaylorIdeal 3 (embeddedCuspIdeal p)) => normalExponentDegree a.val))
    (hComp : adaptedIdeal Q.ideal x Φ hΦ0 =
      weightedCompression (fun a : actualInitialVertices MonomialOrder.degLex
        (analyticZeroTaylorIdeal 3 (embeddedCuspIdeal p)) => normalExponentDegree a.val) Γ)
    (k : ℕ)
    (S : ActualFixedInheritedSelector (actualInitialVertices MonomialOrder.degLex
      (analyticZeroTaylorIdeal 3 (embeddedCuspIdeal p))))
    (e : Fin k ≃ actualInitialVertices MonomialOrder.degLex
      (analyticZeroTaylorIdeal 3 (embeddedCuspIdeal p)))
    (w : Fin k → CoordinateWord 3)
    (hWords : ∀ i, wordExponent (w i) = (e i).val)
    (hFive : ActualHistoricalFivePointLaws S e w Γ)
    (hSpan : Ideal.span (range (fun i => Γ (e i))) = embeddedCuspIdeal p)
    (hAdaptedP : adaptedIdeal P.ideal x Φ hΦ0 =
      Ideal.span {(normalCoordinate 2 1 0)^2, tangentPullback 2 1 (cuspGerm p)}) :

    ∃ D : Opens X, x ∈ D ∧ D ≤ U ∧
      MarkedIdeal.pullback (Subtype.val : D → X) Q =
        MarkedIdeal.pullback (Subtype.val : D → X) P ∧
      NativeHSState (X := CMfd.of (n := 3) D)
        (MarkedIdeal.pullback (Subtype.val : D → X) P)
        ((Subtype.val : D → X) ⁻¹' W) H := by
  have hd := hMark.trans ((embedded_cusp_native_mark p hp).trans hPMark.symm)
  have hI := hComp.trans ((cusp_compression_of_aligned_historical_point_laws p hp k S e w hWords Γ
    hFive hSpan).trans hAdaptedP.symm)
  obtain ⟨D,hxD,hDU,hEq⟩ := exists_open_marked_record_agreement_of_adaptedIdeal_eq
    hQ.2.2.2.1 hP hN hE hd x Φ hΦ0 hI U hx
  exact ⟨D,hxD,hDU,hEq,hEq ▸ hQ.restrict D⟩

end
end Hironaka.HironakaG8OddCuspNativeWindowAgreement
