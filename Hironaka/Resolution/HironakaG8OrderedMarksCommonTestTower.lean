import Hironaka.Resolution.HironakaG8CommonTowerNonmonomialOrders

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace

namespace Hironaka.HironakaG8OrderedMarksCommonTestTower
noncomputable section

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal
  IdealWeightPowers GermIdealOrder NonmonomialOrderLocal DivisorExponentAlong
  HironakaCoherentTransformExtension HironakaG8CommonTowerNonmonomialOrders

set_option maxHeartbeats 1000000 in
/-- The accumulated exceptional divisor compares the two controlled ideals
on the literal common chart of an ambient tower. -/
theorem ordered_marks_common_tower_factor_of_test
    {n : ℕ} {X Y : CMfd.{0} n} (P : MarkedIdeal n X)
    (hN : P.N = univ) (hP : P.ideal.IsCoherent)
    {q : ℕ} (hq : P.d ≤ q) (T : BlowupTower X Y)
    (hPT : IsGeoTestTower P T) (hQT : IsGeoTestTower ({P with d := q}) T) :
    let A := geoTransformAlong P T
    let B := geoTransformAlong ({P with d := q}) T
    A.ideal = (idealPow (BlowupTowerTransforms.exceptionalDivisor T).ideal (q - P.d)).mul B.ideal ∧
      B.cosupp ⊆ A.cosupp := by
  intro A B
  let Q : MarkedIdeal n X := {P with d := q}
  let L := (BlowupTowerTransforms.exceptionalDivisor T).ideal
  let F := idealPow L (q - P.d)
  obtain ⟨hAN, hAc, hAt⟩ := pullback_eq_mul_geoTransformAlong (𝔪 := P) hN hP T hPT
  obtain ⟨hBN, hBc, hBt⟩ := pullback_eq_mul_geoTransformAlong (𝔪 := Q) hN hP T hQT
  have hLi : L.IsInvertible := (BlowupTowerTransforms.exceptionalDivisor T).isInvertible
  have hLc := DivisorMetric.isCoherent_of_isInvertible hLi
  have hFc : F.IsCoherent := GermIdealPullbackCalculus.isCoherent_idealPow hLc _
  have hPow := GermIdealPullbackCalculus.isCoherent_idealPow hLc P.d
  have hPc := IdealWeightPowers.isCoherent_mul hFc hBc
  have hEq : (idealPow L P.d).mul A.ideal = (idealPow L P.d).mul (F.mul B.ideal) := by
    change GermIdeal.pullback (m := n) T.proj P.ideal = (idealPow L P.d).mul A.ideal at hAt
    change GermIdeal.pullback (m := n) T.proj P.ideal = (idealPow L q).mul B.ideal at hBt
    rw [← GermIdealTotalTransform.mul_assoc hPow hFc hBc, ← RestrictLeCalculus.idealPow_add hLc,
      Nat.add_sub_of_le hq, ← hBt, hAt]
  have hCancel := congrArg (fun I => InvertibleIdealQuotient.colon I (idealPow L P.d)) hEq
  have hI := BlowupExceptionalDivisor.isInvertible_idealPow hLi P.d
  rw [BlowupControlledTransform.colon_mul_eq hI hAc,
    BlowupControlledTransform.colon_mul_eq hI hPc] at hCancel
  have hLe : A.ideal.Le B.ideal := by
    rw [hCancel]
    exact GermIdealPullbackCalculus.mul_le_right (fun {_ _} hg =>
      RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hFc hg) hBc
  refine ⟨hCancel, ?_⟩
  intro z hz
  have hNAB : A.N = B.N := hAN.trans hBN.symm
  have hdz : A.d ≤ B.d := by
    change (geoTransformAlong P T).d ≤ (geoTransformAlong Q T).d
    simpa using hq
  change z ∈ cosupport n A.N A.ideal A.d
  rw [hNAB]
  exact DerivativeIdealTower.cosupport_subset_of_le hLe A.d (cosupport_anti hdz hz)

set_option maxHeartbeats 1000000 in
/-- The whole lower-mark record accepts every actual blowup tested by the
higher-mark record. Its controlled ideal and raw cosupport also satisfy
the accumulated comparison at the terminal stage of each prefix. -/
theorem ordered_marks_common_tower_factor
    {n : ℕ} {X Y : CMfd.{0} n} (P : MarkedIdeal n X)
    (hN : P.N = univ) (hP : P.ideal.IsCoherent)
    {q : ℕ} (hq : P.d ≤ q) (T : BlowupTower X Y)
    (hQT : IsGeoTestTower ({P with d := q}) T) :
    let A := geoTransformAlong P T
    let B := geoTransformAlong ({P with d := q}) T
    IsGeoTestTower P T ∧
    A.ideal = (idealPow (BlowupTowerTransforms.exceptionalDivisor T).ideal (q - P.d)).mul B.ideal ∧
      B.cosupp ⊆ A.cosupp := by
  let Q : MarkedIdeal n X := {P with d := q}
  have hPT : IsGeoTestTower P T := by
    induction T with
    | refl => trivial
    | step T C π hπ ih =>
      obtain ⟨hQT, hQC⟩ := hQT
      have hPT := ih hQT
      have hCos := (ordered_marks_common_tower_factor_of_test P hN hP hq T hPT hQT).2
      have hBoundary := geoTransformAlong_E_eq_of_E_eq (𝔍 := P) (𝔪 := Q) rfl T
      exact ⟨hPT, hQC.1, hQC.2.1.trans hCos, hBoundary.symm ▸ hQC.2.2⟩
  exact ⟨hPT, ordered_marks_common_tower_factor_of_test P hN hP hq T hPT hQT⟩

/-- The lower test and whole first-order equality follow from the original
higher-mark finite test. -/
theorem ordered_marks_common_tower_orders
    {n : ℕ} (hn : 0 < n) {X Y : CMfd.{0} n}
    (P : MarkedIdeal n X) (hp : P.IsWellFormed) (hN : P.N = univ)
    (hnP : ∀ x ∈ P.N, IsNonzeroAlongAt P.N P.ideal x)
    {q : ℕ} (hq : P.d ≤ q) (T : BlowupTower X Y)
    (hQT : IsGeoTestTower ({P with d := q}) T) :
    let A := geoTransformAlong P T
    let B := geoTransformAlong ({P with d := q}) T
    IsGeoTestTower P T ∧ A.N = B.N ∧ A.E = B.E ∧
    A.ideal = (idealPow (BlowupTowerTransforms.exceptionalDivisor T).ideal (q - P.d)).mul B.ideal ∧
    B.cosupp ⊆ A.cosupp ∧ nmPart A = nmPart B ∧ (∀ z, nmOrd A z = nmOrd B z) := by
  obtain ⟨hPT, hFac, hCos⟩ := ordered_marks_common_tower_factor P hN hp.isCoherent hq T hQT
  obtain ⟨hCarrier, hBoundary, hPart, hOrder⟩ := common_mark_tower_orders hn P hp hnP q T hPT hQT
  exact ⟨hPT, hCarrier, hBoundary, hFac, hCos, hPart, hOrder⟩

end
end Hironaka.HironakaG8OrderedMarksCommonTestTower
