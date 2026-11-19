import Hironaka.Resolution.HironakaG1ClosedNormalLaws
import Hironaka.Resolution.HironakaG11PresLineChart

/-! Assembly of the closed-normal native state from the two adapted whole-ideal dictionaries. -/
set_option autoImplicit false
open Set Classical
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG1ClosedNormalNativeState
noncomputable section

open HolGerm Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers
  HironakaActualHistoricalNativeStageStep HironakaActualHistoricalNormalizedWeakPresentation
  HironakaActualCauchyMonomialDivision HironakaActualFixedInheritedSelector
  HironakaActualWeightedCoefficientCompression HironakaRelativeNormalMonomialBasis
  HironakaRelativeNormalIdeal HironakaHolomorphicJetMonomialSpan
  HironakaHolomorphicJetChartInvariance HironakaG11PresLineState
  HironakaActualNativeSourceChartComposition HironakaSmoothSubmersionGermIdealColon
  HironakaG1ClosedNormalLaws HironakaG1ClosedNormalSelector

variable {n k : ℕ} {V : Finset (Fin n →₀ ℕ)}

/-- The uncompressed family spans the full extension plus the actual
linear normal equation. -/
theorem span_normalGerms (a : Fin k ≃ V) (Γ : V → HolGerm (ComplexModel n)) :
    Ideal.span (range (fun i => normalGerms Γ (normalEnumeration a i))) =
      Ideal.map (tangentPullback n 1).toRingHom (Ideal.span (range (fun i => Γ (a i)))) ⊔
        Ideal.span {coordinateGerm (Fin.last n)} := by
  rw [Ideal.map_span, ← Set.range_comp, ← Ideal.span_union]
  apply congrArg Ideal.span
  ext g
  constructor
  · rintro ⟨j,rfl⟩
    refine Fin.cases ?_ (fun i => ?_) j
    · exact Or.inr (Set.mem_singleton_iff.mpr (by simp only [normalEnumeration_zero, normalGerms_normal]))
    · exact Or.inl ⟨i, by simp only [normalEnumeration_succ, normalGerms_old]; rfl⟩
  · rintro (⟨i,rfl⟩ | h)
    · exact ⟨i.succ, by simp only [normalEnumeration_succ, normalGerms_old]; rfl⟩
    · rw [Set.mem_singleton_iff] at h
      exact ⟨0, by simp only [normalEnumeration_zero, normalGerms_normal, h]⟩

section Point

variable {X : CMfd.{0} n} {Y : CMfd.{0} (n+1)}
  {W : Set X} {D : Set Y} {P : MarkedIdeal n X} {Q : MarkedIdeal (n+1) Y}

/-- The two geometric equalities needed on a chosen closed-normal chart.
The first concerns the underlying reduced subspace ideal. The second concerns
the actual marked ideal, with the original mark on the normal equation. -/
def ClosedNormalAdaptedChart (x : X) (y : Y)
    (Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel n) x x))
    (hΦ : Φ.toFun (chartAt (ComplexModel n) x x) = 0) : Prop :=
  ∃ (Ψ : LocalHolomorphicEquivAt (chartAt (ComplexModel (n+1)) y y))
    (_ : Ψ.source ⊆ (chartAt (ComplexModel (n+1)) y).target)
    (hΨ : Ψ.toFun (chartAt (ComplexModel (n+1)) y y) = 0),
    adaptedIdeal (vanishingIdeal (n := n+1) D) y Ψ hΨ =
      Ideal.map (tangentPullback n 1).toRingHom
        (adaptedIdeal (vanishingIdeal (n := n) W) x Φ hΦ) ⊔
        Ideal.span {coordinateGerm (Fin.last n)} ∧
    adaptedIdeal Q.ideal y Ψ hΨ =
      Ideal.map (tangentPullback n 1).toRingHom (adaptedIdeal P.ideal x Φ hΦ) ⊔
        Ideal.span {(coordinateGerm (Fin.last n)) ^ P.d}

/-- One actual original native point and its two closed-normal chart
identities produce the extended native point. No target germ family, prefix
data, or ideal generation on the target is supplied. -/
theorem nativePoint_closedNormal
    (S : ActualFixedInheritedSelector V) (a : Fin k ≃ V)
    (w : Fin k → CoordinateWord n) (hw : ∀ i, wordExponent (w i) = (a i).val)
    (hPos : ∀ v : V, 0 < normalExponentDegree v.val)
    (hW : (vanishingIdeal (n := n) W).IsCoherent)
    (hD : (vanishingIdeal (n := n+1) D).IsCoherent)
    (hMark : P.d = weightedCommonMark (fun v : V => normalExponentDegree v.val))
    (x : X) (y : Y)
    (hAt : ActualHistoricalNativePointPresentation S a w W P x)
    (hChart : ∀ (Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel n) x x)),
      Φ.source ⊆ (chartAt (ComplexModel n) x).target →
      ∀ hΦ : Φ.toFun (chartAt (ComplexModel n) x x) = 0,
      ClosedNormalAdaptedChart (W := W) (D := D) (P := P) (Q := Q) x y Φ hΦ) :
    ActualHistoricalNativePointPresentation (normalSelector S) (normalEnumeration a)
      (HironakaG1ClosedNormalDivision.normalWords w) D Q y := by
  obtain ⟨Φ,hΦsrc,hΦ,Γ,hFive,hSpan,hComp⟩ := hAt
  obtain ⟨Ψ,hΨsrc,hΨ,hWhole,hMarked⟩ := hChart Φ hΦsrc hΦ
  have hOld := actual_original_translated_flattened_vanishing_origin_eq_adapted
    x Φ hΦsrc hΦ W hW
  have hNew := actual_original_translated_flattened_vanishing_origin_eq_adapted
    y Ψ hΨsrc hΨ D hD
  refine ⟨Ψ,hΨsrc,hΨ,normalGerms Γ,actualHistoricalFivePointLaws_closedNormal S a w Γ hw hPos hFive,?_,?_⟩
  · rw [span_normalGerms a Γ, hSpan, hOld, hNew, hWhole]
  · rw [hMarked, hComp, hMark, weightedCompression_closedNormal a Γ]

/-- Derive the ambient closed-normal native state from the original state.
The hypotheses on the ambient output are the true HS cut and bound, and
the two whole-ideal chart identities at points of the padded cosupport. -/
theorem nativeHSState_closedNormal (H : ℕ → ℕ) (hP : NativeHSState P W H)
    (hD : IsComplexAnalyticSubset (n := n+1) D) (hN : Q.N = univ)
    (hQI : Q.ideal.IsCoherent) (hMark : Q.d = P.d)
    (hCut : Q.cosupp = {y | ∀ q, hilbertSamuelAt (vanishingIdeal (n := n+1) D) y q = H q})
    (hBound : ∀ y q, hilbertSamuelAt (vanishingIdeal (n := n+1) D) y q ≤ H q)
    (hChart : ∀ y ∈ Q.cosupp, ∃ x ∈ P.cosupp,
      ∀ (Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel n) x x)),
        Φ.source ⊆ (chartAt (ComplexModel n) x).target →
        ∀ hΦ : Φ.toFun (chartAt (ComplexModel n) x x) = 0,
        ClosedNormalAdaptedChart (W := W) (D := D) (P := P) (Q := Q) x y Φ hΦ) :
    NativeHSState Q D H := by
  obtain ⟨hSing,hW,_,_,V,S,k,a,w,hw,hPos,hOwn,hPMark,_,_,hAt⟩ := hP
  refine ⟨hSing,hD,hN,hQI,normalVertices V,normalSelector S,k+1,normalEnumeration a,
    HironakaG1ClosedNormalDivision.normalWords w,normalEnumeration_words a w hw,
    normalVertices_positive hPos,normalWords_owner w hOwn,?_,hCut,hBound,?_⟩
  · rw [hMark,hPMark,weightedCommonMark_closedNormal a]
  · intro y hy
    obtain ⟨x,hx,hxy⟩ := hChart y hy
    exact nativePoint_closedNormal S a w hw hPos
      (CartanIrreducible.cartanCoherence W hW) (CartanIrreducible.cartanCoherence D hD)
      hPMark x y (hAt x hx) hxy

end Point

#print axioms nativeHSState_closedNormal

end
end Hironaka.HironakaG1ClosedNormalNativeState
