import Hironaka.Resolution.HironakaG8CommonTowerNonmonomialOrders
import Hironaka.Resolution.HironakaSharpActualChronologicalResidualDictionary
import Hironaka.Invariant.CanonicalCentres

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace

namespace Hironaka.HironakaG8SharedResidualActiveOrder
noncomputable section

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal IdealWeightPowers GermIdealOrder
  NonmonomialOrderLocal DivisorExponentAlong HironakaCoherentTransformExtension
  HironakaG8CommonTowerNonmonomialOrders RelativePrincipalizationSpan
  HironakaSharpActualChronologicalResidualDictionary CanonicalCentres HomogenizedIdealAlong

set_option maxHeartbeats 1000000 in
/-- At arbitrary common prefixes, initial containment and ordered marks preserve
raw controlled ideal containment on whole ambient carriers. -/
theorem controlled_ideal_le_of_initial_le
    {n : ℕ} {X Y : CMfd.{0} n} (P Q : MarkedIdeal n X)
    (hPN : P.N = univ) (hQN : Q.N = univ)
    (hp : P.ideal.IsCoherent) (hq : Q.ideal.IsCoherent)
    (hI : P.ideal.Le Q.ideal) (hd : P.d ≤ Q.d) (T : BlowupTower X Y)
    (hpT : IsGeoTestTower P T) (hqT : IsGeoTestTower Q T) :
    let A := geoTransformAlong P T
    let B := geoTransformAlong Q T
    A.ideal.Le B.ideal ∧ B.cosupp ⊆ A.cosupp := by
  intro A B
  let L := (BlowupTowerTransforms.exceptionalDivisor T).ideal
  let F := idealPow L (Q.d - P.d)
  obtain ⟨hAN, hAc, hAt⟩ := pullback_eq_mul_geoTransformAlong (𝔪 := P) hPN hp T hpT
  obtain ⟨hBN, hBc, hBt⟩ := pullback_eq_mul_geoTransformAlong (𝔪 := Q) hQN hq T hqT
  have hLi : L.IsInvertible := (BlowupTowerTransforms.exceptionalDivisor T).isInvertible
  have hLc := DivisorMetric.isCoherent_of_isInvertible hLi
  have hFc : F.IsCoherent := GermIdealPullbackCalculus.isCoherent_idealPow hLc _
  have hPow := GermIdealPullbackCalculus.isCoherent_idealPow hLc P.d
  have hPc := IdealWeightPowers.isCoherent_mul hFc hBc
  have hLe : ((idealPow L P.d).mul A.ideal).Le ((idealPow L P.d).mul (F.mul B.ideal)) := by
    change GermIdeal.pullback (m := n) T.proj P.ideal = (idealPow L P.d).mul A.ideal at hAt
    change GermIdeal.pullback (m := n) T.proj Q.ideal = (idealPow L Q.d).mul B.ideal at hBt
    rw [← hAt, ← GermIdealTotalTransform.mul_assoc hPow hFc hBc,
      ← RestrictLeCalculus.idealPow_add hLc, Nat.add_sub_of_le hd, ← hBt]
    exact GermIdealPullbackCalculus.pullback_le_pullback hI
  have hCancel : (InvertibleIdealQuotient.colon ((idealPow L P.d).mul A.ideal) (idealPow L P.d)).Le
      (InvertibleIdealQuotient.colon ((idealPow L P.d).mul (F.mul B.ideal)) (idealPow L P.d)) := by
    intro x f hf
    exact ⟨hf.1, fun g hg => hLe x _ (hf.2 g hg)⟩
  have hInv := BlowupExceptionalDivisor.isInvertible_idealPow hLi P.d
  rw [BlowupControlledTransform.colon_mul_eq hInv hAc,
    BlowupControlledTransform.colon_mul_eq hInv hPc] at hCancel
  have hAB := fun x f hf => GermIdealPullbackCalculus.mul_le_right
    (fun {_ _} hg => GermIdeal.IsCoherent.holomorphicAt_mem hFc hg) hBc x f (hCancel x f hf)
  refine ⟨hAB, ?_⟩
  intro z hz
  have hdAB : A.d ≤ B.d := by change (geoTransformAlong P T).d ≤ (geoTransformAlong Q T).d; simpa using hd
  change z ∈ cosupport n A.N A.ideal A.d
  rw [show A.N = B.N from hAN.trans hBN.symm]
  exact DerivativeIdealTower.cosupport_subset_of_le hAB A.d (cosupport_anti hdAB hz)

/-- The actual higher TEST is also a lower TEST for an initially contained
ideal with the same ambient carrier and ordered boundary. -/
theorem lower_test_of_contained_ideal
    {n : ℕ} {X Y : CMfd.{0} n} (P Q : MarkedIdeal n X)
    (hPN : P.N = univ) (hQN : Q.N = univ)
    (hp : P.ideal.IsCoherent) (hq : Q.ideal.IsCoherent)
    (hI : P.ideal.Le Q.ideal) (hd : P.d ≤ Q.d) (hE : P.E = Q.E)
    (T : BlowupTower X Y) (hqT : IsGeoTestTower Q T) : IsGeoTestTower P T := by
  induction T with
  | refl => trivial
  | step S C π hπ ih =>
    obtain ⟨hqS, hqC⟩ := hqT
    have hpS := ih hqS
    have hCos := (controlled_ideal_le_of_initial_le P Q hPN hQN hp hq hI hd S hpS hqS).2
    have hBoundary := geoTransformAlong_E_eq_of_E_eq hE S
    exact ⟨hpS, hqC.1, hqC.2.1.trans hCos, hBoundary.symm ▸ hqC.2.2⟩

/-- On a phase whose higher record is factor-free and capped at the high
mark, its entire actual active cosupport lies in the low cosupport and both
nonmonomial orders there are exactly the high mark. -/
theorem active_top_order_of_shared_residual
    {n : ℕ} (hn : 0 < n) {X Y : CMfd.{0} n} (P Q : MarkedIdeal n X)
    (hp : P.IsWellFormed) (hq : Q.IsWellFormed) (hPN : P.N = univ) (hQN : Q.N = univ)
    (hnP : ∀ x ∈ P.N, IsNonzeroAlongAt P.N P.ideal x)
    (hnQ : ∀ x ∈ Q.N, IsNonzeroAlongAt Q.N Q.ideal x)
    (hI : P.ideal.Le Q.ideal) (hd : P.d ≤ Q.d) (hE : P.E = Q.E)
    (hPart : nmPart P = nmPart Q) (T : BlowupTower X Y) (hqT : IsGeoTestTower Q T)
    (hNo : let B := geoTransformAlong Q T
      ∀ z ∈ B.N, ∀ i : Fin B.E.length, z ∈ B.E.get i →
        ∃ g, B.ideal.mem z g ∧
          ¬ IsInSpanOnAt (n := n) B.N ((vanishingIdeal (n := n) (B.E.get i)).mem z) z g)
    (hCap : let B := geoTransformAlong Q T
      IsMaximalOrderAlong B.N B.ideal B.d) :
    let A := geoTransformAlong P T
    let B := geoTransformAlong Q T
    IsGeoTestTower P T ∧ B.cosupp ⊆ A.cosupp ∧ nmPart A = nmPart B ∧
      (∀ z ∈ B.cosupp, nmOrd A z = B.d ∧ nmOrd B z = B.d) := by
  intro A B
  have hpT := lower_test_of_contained_ideal P Q hPN hQN hp.isCoherent hq.isCoherent hI hd hE T hqT
  have hCos := (controlled_ideal_le_of_initial_le P Q hPN hQN hp.isCoherent hq.isCoherent hI hd T hpT hqT).2
  have hN := hPN.trans hQN.symm
  have hAB := common_test_tower_nonmonomial_part hn P Q hp hq hnP hnQ hN hE hPart T hpT hqT
  have hAW : A.N = B.N := geoTransformAlong_N_eq_of_N_eq hN T
  have hBW := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hq T hqT
  have hnz := isNonzeroAlongAt_geoTransformAlong_sameCarrier
    hq.isClosedSubmanifold_N hq.isCoherent rfl hnQ T hqT
  have hBN : B.N = univ := (pullback_eq_mul_geoTransformAlong (𝔪 := Q) hQN hq.isCoherent T hqT).1
  have hB : nmPart B = B.ideal := by
    change MonomialPartAlong.nonmonomialPartAlong n (geoTransformAlong Q T).N
      (geoTransformAlong Q T).ideal (geoTransformAlong Q T).E = B.ideal
    rw [nonmonomialPartAlong_eq_restrictOn_of_no_member_factor
      hBW.isClosedSubmanifold_N hBW.isSNCDivisor hBW.isTransverse hBW.isCoherent hNo]
    change RestrictedIdealExtension.restrictOn n B.N B.ideal = B.ideal
    rw [hBN, BlowupTowerTransforms.restrictOn_univ hBW.isCoherent]
  refine ⟨hpT, hCos, hAB, fun z hz => ?_⟩
  have hGe : z ∈ ordGe B B.d := by
    change z ∈ cosupport n B.N (nmPart B) B.d
    rw [hB]
    exact hz
  have hLt : z ∉ ordGe B (B.d + 1) := by
    change z ∉ cosupport n B.N (nmPart B) (B.d + 1)
    rw [hB]
    exact hCap z
  have hOrder := le_antisymm (nmOrd_le_of_notMem hLt)
    ((mem_ordGe_iff hBW hnz (B.cosupp_subset_N hz) _).mp hGe)
  have hSame : nmOrd A z = nmOrd B z := nmOrd_congr fun j => by
    change z ∈ cosupport n A.N (nmPart A) j ↔ z ∈ cosupport n B.N (nmPart B) j
    rw [hAW, hAB]
  exact ⟨hSame.trans hOrder, hOrder⟩

end
end Hironaka.HironakaG8SharedResidualActiveOrder
