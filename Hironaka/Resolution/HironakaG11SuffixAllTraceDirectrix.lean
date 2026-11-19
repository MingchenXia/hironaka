import Hironaka.Resolution.HironakaG11SuffixTraceDirectrix

set_option autoImplicit false

/-! Transfer every retained old-member trace through the same actual birth
and test suffix, using the above-mark directrix comparison. -/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG11SuffixAllTraceDirectrix
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupStrictSubmanifold BlowupSpaceTangent HomogenizedGlueingTower
  MemberInterTowerAlong MarkedIdeals MarkedIdeals.MarkedIdeal
  NormalCrossings GermIdealOrder DivisorExponentAlong HironakaG8LocalHistory
  HironakaG11InvBMClass HironakaG11InvBMLower HironakaG11SuffixTraceDirectrix

/-- If each retained endpoint member is the strict image of a smooth old
source member whose centre germ is contained in it, a single exceptional
sum divisibility gives containment of the other entire endpoint trace in
every retained member. -/
theorem suffix_all_traces_transfer_of_above_mark
    {n : ℕ} (hn : 0 < n) {X Y Z : CMfd.{0} n} (P Q : MarkedIdeal n X)
    (h : LocWPEquiv P Q) (hP : IsClosedSubmanifold n P.N) (hQ : IsClosedSubmanifold n Q.N)
    (hIP : P.ideal.IsCoherent) (hIQ : Q.ideal.IsCoherent) (hE : IsSNCDivisor n P.E)
    (hd1 : 1 ≤ P.d) (hd : Q.d = P.d) (hdim : SameCarrierDim P Q)
    {C : Set X} {π : Y → X} (hπ : IsBlowupAlong n C π)
    (hCP : C ⊆ P.N) (hCQ : C ⊆ Q.N)
    (A B : MarkedIdeal n Y) (hA : A.IsWellFormed) (hB : B.IsWellFormed)
    (hAN : A.N = geoStrictTransform π C P.N) (hBN : B.N = geoStrictTransform π C Q.N)
    (hAD : π ⁻¹' C ∈ A.E) (hBD : π ⁻¹' C ∈ B.E)
    (T : BlowupTower Y Z) (hTA : IsGeoTestTower A T) (hTB : IsGeoTestTower B T)
    {S : List (Set Z)} (hS : ∀ K ∈ S, IsClosed K) (e : ℕ) {z : Z}
    (hzA : z ∈ strictAlong T A.N) (hzD : z ∈ strictAlong T (π ⁻¹' C))
    (hdiv : IsDivNearAlong n (strictAlong T A.N) (exceptionalTermBM (n := n) S e)
      (strictAlong T (π ⁻¹' C)) 1 z)
    (hdata : ∀ᶠ x in 𝓝 (π (T.proj z)), x ∈ C → x ∈ P.cosupp ∧
      IsNonzeroAlongAt P.N P.ideal x ∧ IsNonzeroAlongAt Q.N Q.ideal x ∧
      x ∈ cosupport n P.N P.ideal (P.d+1))
    (hsource : ∀ K ∈ S, ∃ H : Set X, IsClosedSubmanifold n H ∧
      IsClosedSubmanifold n (geoStrictTransform π C H) ∧
      K = strictAlong T (geoStrictTransform π C H) ∧
      ∀ᶠ x in 𝓝 (π (T.proj z)), x ∈ C → x ∈ H) :
    ∀ᶠ w in 𝓝 z, w ∈ strictAlong T B.N → w ∈ strictAlong T (π ⁻¹' C) →
      ∀ K ∈ S, w ∈ K := by
  have hEach : ∀ i : Fin S.length, ∀ᶠ w in 𝓝 z, w ∈ strictAlong T B.N →
      w ∈ strictAlong T (π ⁻¹' C) → w ∈ S.get i := by
    intro i
    obtain ⟨H,hH,hK,heq,hCH⟩ := hsource (S.get i) (List.get_mem _ _)
    have hmem : strictAlong T (geoStrictTransform π C H) ∈ S := heq ▸ List.get_mem _ _
    have ht := suffix_trace_transfer_of_above_mark hn P Q h hP hQ hIP hIQ hE hd1 hd hdim
      hπ hH hCP hCQ A B hA hB hAN hBN hAD hBD hK T hTA hTB hS hmem e hzA hzD hdiv hCH hdata
    simpa only [heq] using ht
  have hall := eventually_all.mpr hEach
  filter_upwards [hall] with w hw hwB hwD K hK
  obtain ⟨i,hi⟩ := List.mem_iff_get.mp hK
  simpa only [hi] using hw i hwB hwD

end Hironaka.HironakaG11SuffixAllTraceDirectrix
