import Hironaka.Resolution.HironakaG11BirthTraceDirectrix
import Hironaka.Resolution.HironakaG11TraceGermTransport

set_option autoImplicit false

/-! A positive-order directrix comparison transports an actual old-member
trace through its birth and the literal subsequent test suffix. -/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG11SuffixTraceDirectrix
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupStrictSubmanifold BlowupSpaceTangent HomogenizedGlueingTower
  MemberInterTowerAlong MarkedIdeals MarkedIdeals.MarkedIdeal
  NormalCrossings GermIdealOrder DivisorExponentAlong HironakaG8LocalHistory
  HironakaG11InvBMClass HironakaG11InvBMLower HironakaG11BirthTraceDirectrix
  HironakaG11TraceGermReflection HironakaG11TraceGermTransport

/-- Divisibility on one literal suffix trace forces the other trace into the
same old strict member, when the genuine source records have the stated
above-mark directrix data along their common birth centre. -/
theorem suffix_trace_transfer_of_above_mark
    {n : ℕ} (hn : 0 < n) {X Y Z : CMfd.{0} n} (P Q : MarkedIdeal n X)
    (h : LocWPEquiv P Q) (hP : IsClosedSubmanifold n P.N) (hQ : IsClosedSubmanifold n Q.N)
    (hIP : P.ideal.IsCoherent) (hIQ : Q.ideal.IsCoherent) (hE : IsSNCDivisor n P.E)
    (hd1 : 1 ≤ P.d) (hd : Q.d = P.d) (hdim : SameCarrierDim P Q)
    {C H : Set X} {π : Y → X} (hπ : IsBlowupAlong n C π)
    (hH : IsClosedSubmanifold n H) (hCP : C ⊆ P.N) (hCQ : C ⊆ Q.N)
    (A B : MarkedIdeal n Y) (hA : A.IsWellFormed) (hB : B.IsWellFormed)
    (hAN : A.N = geoStrictTransform π C P.N) (hBN : B.N = geoStrictTransform π C Q.N)
    (hAD : π ⁻¹' C ∈ A.E) (hBD : π ⁻¹' C ∈ B.E)
    (hK : IsClosedSubmanifold n (geoStrictTransform π C H))
    (T : BlowupTower Y Z) (hTA : IsGeoTestTower A T) (hTB : IsGeoTestTower B T)
    {S : List (Set Z)} (hS : ∀ K ∈ S, IsClosed K)
    (hmem : strictAlong T (geoStrictTransform π C H) ∈ S) (e : ℕ) {z : Z}
    (hzA : z ∈ strictAlong T A.N) (hzD : z ∈ strictAlong T (π ⁻¹' C))
    (hdiv : IsDivNearAlong n (strictAlong T A.N) (exceptionalTermBM (n := n) S e)
      (strictAlong T (π ⁻¹' C)) 1 z)
    (hCH : ∀ᶠ x in 𝓝 (π (T.proj z)), x ∈ C → x ∈ H)
    (hdata : ∀ᶠ x in 𝓝 (π (T.proj z)), x ∈ C → x ∈ P.cosupp ∧
      IsNonzeroAlongAt P.N P.ideal x ∧ IsNonzeroAlongAt Q.N Q.ideal x ∧
      x ∈ cosupport n P.N P.ideal (P.d+1)) :
    ∀ᶠ w in 𝓝 z, w ∈ strictAlong T B.N → w ∈ strictAlong T (π ⁻¹' C) →
      w ∈ strictAlong T (geoStrictTransform π C H) := by
  have hsource := initial_trace_germ_contained_of_div hn A hA (π ⁻¹' C)
    (geoStrictTransform π C H) hAD hK T hTA hS hmem e hzA hzD hdiv
  have hp : T.proj z ∈ geoStrictTransform π C P.N := by
    rw [← hAN]
    exact strictAlong_subset_preimage T hA.isClosedSubmanifold_N.1 hzA
  have hpC : π (T.proj z) ∈ C :=
    strictAlong_subset_preimage T (hπ.1.1.preimage hπ.contMDiff.continuous) hzD
  have hsource' : ∀ᶠ q in 𝓝 (T.proj z), q ∈ geoStrictTransform π C P.N → π q ∈ C →
      q ∈ geoStrictTransform π C H := by
    filter_upwards [hsource] with q hq hqP hqC
    exact hq ⟨hAN.symm ▸ hqP,hqC⟩
  have htarget := birth_trace_transfer_of_above_mark P Q h hP hQ hIP hIQ hE hd1 hd hdim
    hπ hH hCP hCQ hp hpC hCH hsource' hdata
  have htarget' : ∀ᶠ q in 𝓝 (T.proj z), q ∈ B.N ∩ (π ⁻¹' C) →
      q ∈ geoStrictTransform π C H := by
    filter_upwards [htarget] with q hq hqB
    exact hq (hBN ▸ hqB.1) hqB.2
  exact final_trace_germ_contained_of_initial B hB (π ⁻¹' C) (geoStrictTransform π C H)
    hBD T hTB htarget'

end Hironaka.HironakaG11SuffixTraceDirectrix
