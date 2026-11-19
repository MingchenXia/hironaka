import Hironaka.Resolution.HironakaG8CoefficientBoundaryLocal
import Hironaka.Resolution.HironakaG8PowerCompanionLocal
import Hironaka.Resolution.HironakaG8E4cCompanion
import Hironaka.Resolution.HironakaActualOriginalTrueMarkMaskCompanions

set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set TopologicalSpace
open scoped Topology Manifold ContDiff BigOperators
namespace Hironaka.HironakaG1CoeffCompanionLocal
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  MarkedIdealBiholomorphism MarkedIdealRestrictOpen HomogenizedGlueingTower
  NonmonomialOrderLocal NonmonomialOrderTail ResolutionInvariantSpec
  HomogenizedIdealAlong CoefficientIdeal CompanionRebase IdealWeightPowers
  HironakaG8LocalHistory HironakaG8LocalPower HironakaG8CoefficientBoundaryLocal
  HironakaG8PowerCompanionLocal HironakaG8E4cCompanion HironakaG8MixedBoundaryExponents
  HironakaActualPowerBoundaryExponents HironakaG8PowerNonmonomialOrder HironakaActualInitialNonmonomialCoefficientBoundary
  HironakaActualOriginalTrueMarkMaskCompanions StepOneValue StepOneValueMasked
  HironakaEmbeddedAnalytic InvDomainTowerAlong CompanionOpen

/-- A native record and its coefficient record have locally equivalent
actual companions, at their respective true marks, with empty boundary. -/
theorem coefficient_companions_local {n k : ℕ} (hn : 0 < n) {X : CMfd.{0} n}
    (P : MarkedIdeal n X) (hP : IsInvDomain k P) (hE : P.E = [])
    (o : ℕ) (ho : 1 ≤ o) (hb : ∀ x ∈ P.cosupp, x ∉ ordGe P (o+1)) :
    let e := sumExp (fun j => P.d-j) P.d 0
    LocWPEquiv (companionOf n P o) (companionOf n (coeffMarkedAlong P) (e*o)) := by
  let e := sumExp (fun j => P.d-j) P.d 0
  have he : 1 ≤ e := one_le_sumExp (fun j hj => by omega) 0
  have heo : 1 ≤ e*o := Nat.mul_pos he ho
  have hPow := powerMarked_isInvDomain P hP he
  have hCoeff := coefficient_isInvDomain P hP
  have hp : LocWPEquiv P (powerMarked P e) := locEquiv_powerMarked (κ := Kinds.wp) rfl P hP he
  have hc : LocWPEquiv P (coeffMarkedAlong P) := coefficient_local_any_boundary P hP
  have hbase : LocWPEquiv (powerMarked P e) (coeffMarkedAlong P) := hp.symm.trans hc
  have hN : (coeffMarkedAlong P).N = (powerMarked P e).N := rfl
  have hd : (coeffMarkedAlong P).d = (powerMarked P e).d := by
    change (Finset.range P.d).prod (fun j => (derivMarkedAlong P j).d) = P.d * e
    simpa only [derivMarkedAlong_d,Nat.sub_zero] using
      (mul_sumExp (fun j => P.d-j) (show 0 < P.d from hP.one_le_d) (i := 0)).symm
  have hPE : (powerMarked P e).E = [] := hE
  have hExp : ExpAgree (powerMarked P e) (coeffMarkedAlong P) := expAgree_of_nil hPE
  have hPowBound : ∀ x ∈ (powerMarked P e).cosupp, x ∉ ordGe (powerMarked P e) (e*o+1) := by
    intro x hx hp'
    have hxP : x ∈ P.cosupp := (powerMarked_cosupp P hP he) ▸ hx
    have hxN := P.cosupp_subset_N hxP
    have hhigh := (mem_ordGe_iff hPow.isWellFormed hPow.isNonzeroAlongAt hxN _).mp hp'
    rw [nmOrd_powerMarked hn P hP he hxN] at hhigh
    have hgt : o < nmOrd P x := Nat.lt_of_mul_lt_mul_left (by omega : e*o < e*nmOrd P x)
    exact hb x hxP ((mem_ordGe_iff hP.isWellFormed hP.isNonzeroAlongAt hxN _).mpr (by omega))
  have hpc := locWPEquiv_companionOf_powerMarked hn P hP he ho hb
  have hcc := locWPEquiv_companionOf hbase hPow hCoeff hN hd hExp hn heo hPowBound
  exact hpc.trans hcc

/-- The literal two companions in the original given-Q driver belong to
the full local relation, including alternating blowups, line projections,
and open restrictions. -/
theorem original_coefficient_companions_local {n k : ℕ} (hn : 0 < n) {A : CMfd.{0} n}
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
      x ∈ U ∧ LocWPEquiv (companionOf n P μ) (companionOf n B (e*μ)) := by
  obtain ⟨hm,hL,hEmpty,hx,hμ,_hMask⟩ := original_lower_true_mark_mask hn Q hQ hN hE hMax W hW hSing a ha
  obtain ⟨_hmC,hxU,_hMaskC,hNatural,_hJ,_hK,_hMaxJ,_hMaxK,_hJN,_hKN,_hJE,_hKE,_hJd,_hKd,
    _hCompJ,_hCompK,_hWeak,_hUpper⟩ := original_lower_true_mark_companions hn Q hQ hN hE hMax W hW hSing a ha
  let V := maskB Q (.refl : BlowupTower A A) a
  let L : MarkedIdeal n (CMfd.of (n := n) V) := lowerMarkedB Q (.refl : BlowupTower A A) a
  let x : V := ⟨a,hm⟩
  let μ := nmOrd L x
  let e := sumExp (fun j => L.d-j) L.d 0
  let U := ordMask L μ
  let P : MarkedIdeal n (CMfd.of (n := n) U) := MarkedIdeal.pullback (Subtype.val : U → V) L
  let B : MarkedIdeal n (CMfd.of (n := n) U) := MarkedIdeal.pullback (Subtype.val : U → V) (coeffMarkedAlong L)
  change IsInvDomain (k-1) L at hL
  change L.E = [] at hEmpty
  change L.d ≤ μ at hμ
  change B = coeffMarkedAlong P at hNatural
  have hP : IsInvDomain (k-1) P := isInvDomain_pullback_val U hL
  have hPE : P.E = [] := by
    change L.E.map ((Subtype.val : U → V) ⁻¹' ·) = []
    rw [hEmpty,List.map_nil]
  have hPos : 1 ≤ μ := hL.one_le_d.trans hμ
  have hBound : ∀ z ∈ P.cosupp, z ∉ ordGe P (μ+1) :=
    bound_pullback_val hn hL.isWellFormed hL.isNonzeroAlongAt U
      (fun _ _ hz => notMem_ordGe_of_mem_ordMask hz)
  have hLocal := coefficient_companions_local hn P hP hPE μ hPos hBound
  refine ⟨hm,hxU,?_⟩
  change LocWPEquiv (companionOf n P μ) (companionOf n B (e*μ))
  rw [hNatural]
  exact hLocal

end
end Hironaka.HironakaG1CoeffCompanionLocal
