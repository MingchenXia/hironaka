import Hironaka.Resolution.HironakaG1CoeffCompanionLocal
import Hironaka.Resolution.HironakaG1OriginalStepSkeleton
import Hironaka.Resolution.HironakaG8MemberLoci
set_option autoImplicit false
open Set TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG1GenericPositiveMask
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealEquivalence.MarkedIdeal
  BlowupTowers BlowupTowerTransforms ResolutionInvariantSpec StepOneValue
  HironakaG1OriginalStepSkeleton HironakaG8MemberLoci HironakaG1CoeffCompanionLocal
  HironakaActualOriginalTrueMarkMaskCompanions HironakaEmbeddedAnalytic
  StepOneValueMasked NonmonomialOrderLocal NonmonomialOrderTail HomogenizedIdealAlong
  CoefficientIdeal IdealWeightPowers CompanionRebase MarkedIdealRestrictOpen MarkedIdealBiholomorphism

/-- Equivalent records with the same carrier have equal literal positive
Step 1 masks at every common tested prefix. -/
theorem lowerMask_succ_of_wEquiv {n kA kB : ℕ} (hn : 0 < n) {X Y : CMfd.{0} n}
    (A B : MarkedIdeal n X) (hA : IsInvDomain kA A) (hB : IsInvDomain kB B)
    (hN : A.N = B.N) (hW : WEquiv A B) (T : BlowupTower X Y) (hT : IsGeoTestTower A T)
    (y : Y) (s : ℕ) : lowerMask A (s+1) T y = lowerMask B (s+1) T y := by
  change maskA A T y = maskA B T y
  have hOrig := origMembers_eq_of_E_eq hW.1 T
  have hl : ∀ z : Y, level A T z = level B T z :=
    fun z => (original_step_skeleton_of_wEquiv hn A B hA hB hN hW T hT z).1
  have hs : ∀ z : Y, IsSpecial A T z ↔ IsSpecial B T z :=
    fun z => (original_step_skeleton_of_wEquiv hn A B hA hB hN hW T hT z).2.1
  unfold maskA
  congr 1
  apply congrArg interior
  ext z
  simp only [mem_ofPred_eq,hOrig,hl,hs]

/-- For the original given-Q companion pair, every actual positive-level
Step 1 mask agrees on the whole open at every common tested prefix. -/
theorem original_coefficient_companions_positive_masks {n k : ℕ} (hn : 0 < n) {A : CMfd.{0} n}
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
      x ∈ U ∧ ∀ {Y : CMfd.{0} n} (T : BlowupTower (CMfd.of (n := n) U) Y),
        IsGeoTestTower J T → ∀ (y : Y) (s : ℕ), lowerMask J (s+1) T y = lowerMask K (s+1) T y := by
  obtain ⟨hm,hxU,hLocal⟩ := original_coefficient_companions_local hn Q hQ hN hE hMax W hW hSing a ha
  obtain ⟨_hmC,_hxUC,_hMask,_hNatural,hJ,hK,_hMaxJ,_hMaxK,hJN,hKN,_hJE,_hKE,_hJd,_hKd,
    _hCompJ,_hCompK,_hWeak,_hUpper⟩ := original_lower_true_mark_companions hn Q hQ hN hE hMax W hW hSing a ha
  refine ⟨hm,hxU,?_⟩
  intro Y T hT y s
  exact lowerMask_succ_of_wEquiv hn _ _ hJ hK (hJN.trans hKN.symm) hLocal.wEquiv T hT y s

end
end Hironaka.HironakaG1GenericPositiveMask
