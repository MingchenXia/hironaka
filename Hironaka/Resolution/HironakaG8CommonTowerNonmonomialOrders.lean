import Hironaka.Resolution.HironakaSharpActualMonomialDivisionResidual
import Hironaka.Resolution.HironakaSharpActualTotalNonmonomialTransport
import Hironaka.MarkedIdeal.MarkedIdealOpenBiholomorphism
import Hironaka.Invariant.NonmonomialOrderLocal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace

namespace Hironaka.HironakaG8CommonTowerNonmonomialOrders
noncomputable section

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  GermIdealOrder MonomialPartAlong DivisorExponentAlong NonmonomialOrderLocal
  HironakaCoherentTransformExtension HironakaSharpActualChronologicalStrictStep
  HironakaSharpActualTotalNonmonomialTransport HironakaSharpActualMonomialDivisionResidual

set_option maxHeartbeats 1400000 in
/-- On a common actual tested tower, the whole next total transform can be
replaced by the total transform of its nonmonomial part when computing the
next nonmonomial ideal. Hence the two original ideals need only share their
initial nonmonomial part. -/
theorem common_test_tower_nonmonomial_part
    {n : ℕ} (hn : 0 < n) {X Y : CMfd.{0} n}
    (P Q : MarkedIdeal n X) (hp : P.IsWellFormed) (hq : Q.IsWellFormed)
    (hnP : ∀ x ∈ P.N, IsNonzeroAlongAt P.N P.ideal x)
    (hnQ : ∀ x ∈ Q.N, IsNonzeroAlongAt Q.N Q.ideal x)
    (hN : P.N = Q.N) (hE : P.E = Q.E) (hPart : nmPart P = nmPart Q)
    (T : BlowupTower X Y) (hpT : IsGeoTestTower P T) (hqT : IsGeoTestTower Q T) :
    nmPart (geoTransformAlong P T) = nmPart (geoTransformAlong Q T) := by
  induction T with
  | refl => exact hPart
  | step T C π hπ ih =>
    obtain ⟨hpT, hpC⟩ := hpT
    obtain ⟨hqT, hqC⟩ := hqT
    let A := geoTransformAlong P T
    let B := geoTransformAlong Q T
    have ha := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hp T hpT
    have hb := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hq T hqT
    have hnA := isNonzeroAlongAt_geoTransformAlong_sameCarrier
      hp.isClosedSubmanifold_N hp.isCoherent rfl hnP T hpT
    have hnB := isNonzeroAlongAt_geoTransformAlong_sameCarrier
      hq.isClosedSubmanifold_N hq.isCoherent rfl hnQ T hqT
    have hNA : A.N = B.N := geoTransformAlong_N_eq_of_N_eq hN T
    have hEA : A.E = B.E := geoTransformAlong_E_eq_of_E_eq hE T
    have hAB : nmPart A = nmPart B := ih hpT hqT
    have hStepA := (actual_geoTransform_nonmonomial_eq_total hn A ha hnA hpC hπ).trans
      (actual_whole_total_nonmonomial_parts_transport hn ha.isClosedSubmanifold_N
        ha.isSNCDivisor ha.isTransverse ha.isCoherent hnA hπ hpC.subset_N hpC.2.2)
    have hStepB := (actual_geoTransform_nonmonomial_eq_total hn B hb hnB hqC hπ).trans
      (actual_whole_total_nonmonomial_parts_transport hn hb.isClosedSubmanifold_N
        hb.isSNCDivisor hb.isTransverse hb.isCoherent hnB hπ hqC.subset_N hqC.2.2)
    refine hStepA.trans (Eq.trans ?_ hStepB.symm)
    change nonmonomialPartAlong n (nextTotalMarked A.N A.ideal C π).N
      (nextTotalMarked A.N (nmPart A) C π).ideal (A.geoTransform C π).E =
      nonmonomialPartAlong n (nextTotalMarked B.N B.ideal C π).N
        (nextTotalMarked B.N (nmPart B) C π).ideal (B.geoTransform C π).E
    have hBoundary : (A.geoTransform C π).E = (B.geoTransform C π).E := by
      change A.E.map _ ++ _ = B.E.map _ ++ _
      rw [hEA]
    have hCarrier : (nextTotalMarked A.N A.ideal C π).N =
        (nextTotalMarked B.N B.ideal C π).N := by
      change BlowupStrictSubmanifold.geoStrictTransform π C A.N =
        BlowupStrictSubmanifold.geoStrictTransform π C B.N
      rw [hNA]
    rw [hBoundary, hCarrier, hNA, hAB]

theorem common_mark_tower_orders
    {n : ℕ} (hn : 0 < n) {X Y : CMfd.{0} n}
    (P : MarkedIdeal n X) (hp : P.IsWellFormed)
    (hnP : ∀ x ∈ P.N, IsNonzeroAlongAt P.N P.ideal x)
    (q : ℕ) (T : BlowupTower X Y)
    (hpT : IsGeoTestTower P T) (hqT : IsGeoTestTower ({P with d := q}) T) :
    let A := geoTransformAlong P T
    let B := geoTransformAlong ({P with d := q}) T
    A.N = B.N ∧ A.E = B.E ∧ nmPart A = nmPart B ∧ (∀ z, nmOrd A z = nmOrd B z) := by
  intro A B
  let Q : MarkedIdeal n X := {P with d := q}
  have hq : Q.IsWellFormed := ⟨hp.1, hp.2, hp.3, hp.4⟩
  have hN : A.N = B.N := geoTransformAlong_N_eq_of_N_eq (𝔍 := P) (𝔪 := Q) rfl T
  have hE : A.E = B.E := geoTransformAlong_E_eq_of_E_eq (𝔍 := P) (𝔪 := Q) rfl T
  have he : nmPart A = nmPart B :=
    common_test_tower_nonmonomial_part hn P Q hp hq hnP hnP rfl rfl rfl T hpT hqT
  refine ⟨hN, hE, he, fun z => nmOrd_congr fun j => ?_⟩
  change z ∈ cosupport n A.N (nmPart A) j ↔ z ∈ cosupport n B.N (nmPart B) j
  rw [hN, he]

/-- A tested tower can also be read at mark zero on the same initial record. -/
theorem common_zero_mark_test_tower
    {n : ℕ} {X Y : CMfd.{0} n} (P : MarkedIdeal n X) (hp : P.IsWellFormed)
    (T : BlowupTower X Y) (hT : IsGeoTestTower P T) :
    IsGeoTestTower ({P with d := 0}) T := by
  let Q : MarkedIdeal n X := {P with d := 0}
  have hq : Q.IsWellFormed := ⟨hp.1, hp.2, hp.3, hp.4⟩
  change IsGeoTestTower Q T
  induction T with
  | refl => trivial
  | step T C π hπ ih =>
    obtain ⟨hT, hC⟩ := hT
    have hzT := ih hT
    have hZ := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hq T hzT
    have hN := geoTransformAlong_N_eq_of_N_eq (𝔍 := Q) (𝔪 := P) rfl T
    have hE := geoTransformAlong_E_eq_of_E_eq (𝔍 := Q) (𝔪 := P) rfl T
    refine ⟨hzT, hC.1, ?_, hE.symm ▸ hC.2.2⟩
    unfold MarkedIdeal.cosupp
    rw [d_geoTransformAlong, show Q.d = 0 from rfl]
    rw [cosupport_zero (fun _ _ hg =>
      RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hZ.isCoherent hg), hN]
    exact hC.subset_N

/-- On a whole ambient carrier, the literal pullback of the original whole
ideal gives the same nonmonomial part as the entire controlled history. -/
theorem controlled_tower_nonmonomial_eq_initial_total_pullback
    {n : ℕ} (hn : 0 < n) {X Y : CMfd.{0} n}
    (P : MarkedIdeal n X) (hp : P.IsWellFormed) (hN : P.N = univ)
    (hnP : ∀ x ∈ P.N, IsNonzeroAlongAt P.N P.ideal x)
    (T : BlowupTower X Y) (hT : IsGeoTestTower P T) :
    let A := geoTransformAlong P T
    nmPart A = nonmonomialPartAlong n A.N (GermIdeal.pullback (m := n) T.proj P.ideal) A.E := by
  intro A
  let Q : MarkedIdeal n X := {P with d := 0}
  let B := geoTransformAlong Q T
  have hZT : IsGeoTestTower Q T := common_zero_mark_test_tower P hp T hT
  obtain ⟨hCar, hBound, hPart, _⟩ := common_mark_tower_orders hn P hp hnP 0 T hT hZT
  obtain ⟨_, hCoh, hTot⟩ := pullback_eq_mul_geoTransformAlong (𝔪 := Q) hN hp.isCoherent T hZT
  change GermIdeal.pullback (m := n) T.proj P.ideal =
    (IdealWeightPowers.idealPow (BlowupTowerTransforms.exceptionalDivisor T).ideal 0).mul B.ideal at hTot
  rw [IdealWeightPowers.idealPow_zero, BlowupControlledTransform.unitIdeal_mul hCoh] at hTot
  change nmPart A = nonmonomialPartAlong n A.N (GermIdeal.pullback (m := n) T.proj P.ideal) A.E
  rw [hTot, hCar, hBound]
  exact hPart

end
end Hironaka.HironakaG8CommonTowerNonmonomialOrders
