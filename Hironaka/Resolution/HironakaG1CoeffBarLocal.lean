import Hironaka.Resolution.HironakaG1CoeffCompanionLocal
import Hironaka.Resolution.HironakaG8HomStable
set_option autoImplicit false
open Set TopologicalSpace
open scoped Topology Manifold ContDiff BigOperators
namespace Hironaka.HironakaG1CoeffBarLocal
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms MarkedIdealBiholomorphism
  ResolutionInvariantSpec StepOneValue StepOneValueMasked HironakaG8LocalHistory HironakaG8HomStable
  HironakaG1CoeffCompanionLocal HironakaActualOriginalTrueMarkMaskCompanions HironakaEmbeddedAnalytic
  NonmonomialOrderLocal NonmonomialOrderTail HomogenizedIdealAlong CoefficientIdeal IdealWeightPowers
  CompanionRebase MarkedIdealRestrictOpen

/-- Literal bar records retain full local equivalence for any two native
locally equivalent records, even with arbitrary retained boundaries. -/
theorem bar_local_of_local {n kA kB : ℕ} {X : CMfd.{0} n} (A B : MarkedIdeal n X)
    (hA : IsInvDomain kA A) (hB : IsInvDomain kB B) (h : LocWPEquiv A B) :
    LocWPEquiv (barMarked A) (barMarked B) :=
  ((bar_local_any_boundary A hA).symm.trans h).trans (bar_local_any_boundary B hB)

/-- The original given-Q companions have locally equivalent literal bar
records, including on every open after each actual controlled prefix. -/
theorem original_coefficient_bars_local {n k : ℕ} (hn : 0 < n) {A : CMfd.{0} n}
    (Q : MarkedIdeal n A) (hQ : IsInvDomain k Q) (hN : Q.N = univ) (hE : Q.E = [])
    (hMax : IsMaximalOrderAlong Q.N Q.ideal Q.d) (W : Set A)
    (hW : IsComplexAnalyticSubset (n := n) W) (hSing : Q.cosupp ⊆ singularSet (n := n) W)
    (a : A) (ha : a ∈ Q.cosupp) :
    ∃ hm : a ∈ maskB Q (.refl : BlowupTower A A) a,
      let V := maskB Q (.refl : BlowupTower A A) a
      let L : MarkedIdeal n (CMfd.of (n := n) V) := lowerMarkedB Q (.refl : BlowupTower A A) a
      let x : V := ⟨a,hm⟩
      let μ := nmOrd L x
      let e := sumExp (fun j => L.d-j) L.d 0
      let U := ordMask L μ
      let P : MarkedIdeal n (CMfd.of (n := n) U) := MarkedIdeal.pullback (Subtype.val : U → V) L
      let B : MarkedIdeal n (CMfd.of (n := n) U) := MarkedIdeal.pullback (Subtype.val : U → V) (coeffMarkedAlong L)
      let J := companionOf n P μ
      let K := companionOf n B (e*μ)
      x ∈ U ∧ LocWPEquiv (barMarked J) (barMarked K) ∧
        ∀ {Y : CMfd.{0} n} (T : BlowupTower (CMfd.of (n := n) U) Y), IsGeoTestTower J T →
        ∀ O : Opens Y, LocWPEquiv
          (MarkedIdeal.pullback (M' := CMfd.of (n := n) O) (Subtype.val : O → Y) (geoTransformAlong (barMarked J) T))
          (MarkedIdeal.pullback (M' := CMfd.of (n := n) O) (Subtype.val : O → Y) (geoTransformAlong (barMarked K) T)) := by
  obtain ⟨hm,hxU,hLocal⟩ := original_coefficient_companions_local hn Q hQ hN hE hMax W hW hSing a ha
  obtain ⟨_hmC,_hxUC,_hMask,_hNatural,hJ,hK,_hMaxJ,_hMaxK,_hJN,_hKN,_hJE,_hKE,_hJd,_hKd,
    _hCompJ,_hCompK,_hWeak,_hUpper⟩ := original_lower_true_mark_companions hn Q hQ hN hE hMax W hW hSing a ha
  have hBar := bar_local_of_local _ _ hJ hK hLocal
  refine ⟨hm,hxU,hBar,?_⟩
  intro Y T hT O
  have hTB := (((bar_local_any_boundary _ hJ).wEquiv).2 T).1.mp hT
  exact (hBar.geoTransformAlong T hTB).restrict O
end
end Hironaka.HironakaG1CoeffBarLocal
