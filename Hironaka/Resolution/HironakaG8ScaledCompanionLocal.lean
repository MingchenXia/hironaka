import Hironaka.Resolution.HironakaG8PowerCompanionLocal
import Hironaka.Resolution.HironakaG8E4cCompanion
import Hironaka.Resolution.HironakaG8ScaledNonmonomialHistory
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set Filter Classical TopologicalSpace
open scoped Topology Manifold ContDiff BigOperators
namespace Hironaka.HironakaG8ScaledCompanionLocal
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism ResolutionInvariantSpec
  DivisorExponentAlong IdealWeightPowers NonmonomialOrderLocal NonmonomialOrderTail
  HomogenizedIdealAlong CompanionRebase HironakaG8LocalHistory HironakaG8LocalPower
  HironakaG8PowerCompanionLocal HironakaG8PowerNonmonomialOrder HironakaActualPowerBoundaryExponents
  HironakaG8E4cCompanion HironakaG8MixedBoundaryExponents HironakaG8ScaledNonmonomialHistory

/-- Companions at cross-scaled true orders remain locally equivalent for unequal marks. -/
theorem scaled_companions_local {n k l : ℕ} (hn : 0<n) {X : CMfd.{0} n}
    (P Q : MarkedIdeal n X) (hP : IsInvDomain k P) (hQ : IsInvDomain l Q)
    (hN : Q.N=P.N) (hLocal : LocWPEquiv P Q)
    (hInitial : ∀ D ∈ P.E, ∀ x ∈ P.cosupp, x∈D →
      Q.d*divExpAlong n P.N P.ideal D x=P.d*divExpAlong n Q.N Q.ideal D x)
    {oP oQ : ℕ} (hoP : 1≤oP) (hOrder : Q.d*oP=P.d*oQ)
    (hBoundP : ∀ x ∈ P.cosupp, x ∉ ordGe P (oP+1)) :
    LocWPEquiv (companionOf n P oP) (companionOf n Q oQ) := by
  have hoQ : 1≤oQ := by
    have hq := hQ.one_le_d
    nlinarith only [hq,hoP,hOrder]
  have hBoundQ : ∀ x ∈ Q.cosupp, x ∉ ordGe Q (oQ+1) := by
    intro x hxQ hxHigh
    have hxP : x ∈ P.cosupp := hLocal.wEquiv.cosupp_eq.symm ▸ hxQ
    have hxQN := Q.cosupp_subset_N hxQ
    have hxPN := P.cosupp_subset_N hxP
    have hgtQ : oQ < nmOrd Q x := by
      have h := (mem_ordGe_iff hQ.isWellFormed hQ.isNonzeroAlongAt hxQN _).mp hxHigh
      omega
    have hScale := scaled_nmOrd_of_initial_exponents hn P Q hP hQ hN hLocal.E_eq hLocal hInitial
      (.refl : BlowupTower X X) trivial x hxP
    change Q.d*nmOrd P x=P.d*nmOrd Q x at hScale
    have hgtP : oP < nmOrd P x := by
      have hp := hP.one_le_d
      nlinarith only [hScale,hOrder,hgtQ,hp]
    exact hBoundP x hxP ((mem_ordGe_iff hP.isWellFormed hP.isNonzeroAlongAt hxPN _).mpr (by omega))
  let P' := powerMarked P Q.d
  let Q' := powerMarked Q P.d
  have hP' : IsInvDomain k P' := powerMarked_isInvDomain P hP hQ.one_le_d
  have hQ' : IsInvDomain l Q' := powerMarked_isInvDomain Q hQ hP.one_le_d
  have hLP : LocWPEquiv P P' := locEquiv_powerMarked (κ := Kinds.wp) rfl P hP hQ.one_le_d
  have hLQ : LocWPEquiv Q Q' := locEquiv_powerMarked (κ := Kinds.wp) rfl Q hQ hP.one_le_d
  have hL : LocWPEquiv P' Q' := hLP.symm.trans (hLocal.trans hLQ)
  have hN' : Q'.N=P'.N := hN
  have hd' : Q'.d=P'.d := by change Q.d*P.d=P.d*Q.d; exact Nat.mul_comm _ _
  have hExp : ExpAgree P' Q' := by
    intro D hD x hx hxD
    have hxP : x∈P.cosupp := (powerMarked_cosupp P hP hQ.one_le_d) ▸ hx
    change divExpAlong n P.N (idealPow P.ideal Q.d) D x = divExpAlong n Q.N (idealPow Q.ideal P.d) D x
    rw [divExpAlong_idealPow hP.isWellFormed.isClosedSubmanifold_N hP.isWellFormed.isCoherent hQ.one_le_d x,
      divExpAlong_idealPow hQ.isWellFormed.isClosedSubmanifold_N hQ.isWellFormed.isCoherent hP.one_le_d x]
    exact hInitial D hD x hxP hxD
  have hbP' : ∀ x∈P'.cosupp, x∉ordGe P' (Q.d*oP+1) := by
    intro x hx hp
    have hxP : x∈P.cosupp := (powerMarked_cosupp P hP hQ.one_le_d) ▸ hx
    have hxN := P.cosupp_subset_N hxP
    have hp' := (mem_ordGe_iff hP'.isWellFormed hP'.isNonzeroAlongAt hxN _).mp hp
    rw [nmOrd_powerMarked hn P hP hQ.one_le_d hxN] at hp'
    have hgt : oP < nmOrd P x := Nat.lt_of_mul_lt_mul_left (by omega : Q.d*oP < Q.d*nmOrd P x)
    exact hBoundP x hxP ((mem_ordGe_iff hP.isWellFormed hP.isNonzeroAlongAt hxN _).mpr (by omega))
  have hLeft := locWPEquiv_companionOf_powerMarked hn P hP hQ.one_le_d hoP hBoundP
  have hRight := locWPEquiv_companionOf_powerMarked hn Q hQ hP.one_le_d hoQ hBoundQ
  have hMid := locWPEquiv_companionOf hL hP' hQ' hN' hd' hExp hn (Nat.mul_pos hQ.one_le_d hoP) hbP'
  rw [hOrder] at hLeft hMid
  exact hLeft.trans (hMid.trans hRight.symm)
end
end Hironaka.HironakaG8ScaledCompanionLocal
