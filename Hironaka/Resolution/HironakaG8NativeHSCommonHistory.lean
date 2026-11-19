import Hironaka.Resolution.HironakaG8CanonicalTwoPairFullCuts
import Hironaka.Resolution.HironakaG11PresLineStable
import Hironaka.Resolution.HironakaG1IndependentContactScaledHistory
set_option autoImplicit false
open Set Filter Classical TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG8NativeHSCommonHistory
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  MarkedIdealBiholomorphism ResolutionInvariantSpec CanonicalCentres
  HironakaG8LocalHistory HironakaG11InvBMClass DivisorExponentAlong
  HironakaG11PresLineState HironakaG11PresLineStable HironakaG1IndependentContactScaledHistory
  HironakaG1OriginalUnequalMarkCanonical HironakaG8CanonicalTwoPairFullCuts

/-- Two independently selected native presentations of the SAME HS family,
starting with empty boundary, retain scaled labelled exponents and the exact
full native comparison on every common first-side canonical history. -/
theorem native_hs_common_canonical_history {n k : ℕ} (hn : 0<n)
    {X : CMfd.{0} n} (P Q : MarkedIdeal n X)
    (hP : IsInvDomain k P) (hQ : IsInvDomain k Q)
    (hEP : P.E=[]) (hEQ : Q.E=[])
    {W : Set X} {H : ℕ → ℕ} (hStateP : NativeHSState P W H) (hStateQ : NativeHSState Q W H) :
    LocWPEquiv P Q ∧
    ∀ {Y : CMfd.{0} n} (T : BlowupTower X Y), IsCanonical P ((invFamily hn k).inv P) T →
      IsCanonical Q ((invFamily hn k).inv Q) T ∧
      (∀ D ∈ (geoTransformAlong P T).E, ∀ y ∈ (geoTransformAlong P T).cosupp, y ∈ D →
        Q.d * divExpAlong n (geoTransformAlong P T).N (geoTransformAlong P T).ideal D y =
        P.d * divExpAlong n (geoTransformAlong Q T).N (geoTransformAlong Q T).ideal D y) ∧
      (∀ x ∈ (geoTransformAlong P T).cosupp, ∀ y ∈ (geoTransformAlong P T).cosupp,
        ((invFamily hn k).inv P T x < (invFamily hn k).inv P T y ↔
         (invFamily hn k).inv Q T x < (invFamily hn k).inv Q T y)) := by
  have hL := locWPEquiv_native hStateP hStateQ (hEQ.trans hEP.symm)
  have hN : P.N = Q.N := hStateP.2.2.1.trans hStateQ.2.2.1.symm
  have hDim : SameCarrierDim P Q := SameCarrierDim.of_N_eq hN
  have hI : ∀ D ∈ P.E, ∀ x ∈ P.cosupp, x ∈ D →
      Q.d * divExpAlong n P.N P.ideal D x = P.d * divExpAlong n Q.N Q.ideal D x := by
    intro D hD
    rw [hEP] at hD
    exact (List.not_mem_nil hD).elim
  refine ⟨hL,?_⟩
  intro Y T hCan
  have hT := (invFamily hn k).isInvValue.isGeoTestTower_of_isCanonical hP T hCan
  refine ⟨(invFamily_isCanonical_iff_of_local hn P Q hP hQ hL hDim hI T).mp hCan,?_ ,?_⟩
  · exact scaled_exponents_sameCarrierDim P Q hP hQ hL hDim hI T hT
  · intro x hx y hy
    exact canonical_two_pair_full_cuts hn P Q P Q hP hQ hP hQ hL hDim hI hL hDim hI rfl rfl T T hCan hCan x y hx hy
end
end Hironaka.HironakaG8NativeHSCommonHistory
