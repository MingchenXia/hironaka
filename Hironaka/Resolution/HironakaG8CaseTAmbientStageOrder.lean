import Hironaka.Resolution.HironakaG8CaseTAmbientOrder
import Hironaka.Resolution.HironakaG8CaseTAmbientStage

/-!
# Pointwise order agreement at actual prefixed test stages

The ambient hypersurface witnesses are transported along the very test tower
of the prefixed pair. No additional stagewise geometric data are supplied.
-/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG8CaseTAmbientStageOrder
noncomputable section
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  HomogenizedGlueingTower NormalCrossings DivisorExponentAlong GermIdealOrder
  HironakaG8LocalHistory HironakaG8ClassStepHistory HironakaG8CaseTAmbientStage
open HironakaG11InvBMClass (SameCarrierDim)

/-- The original pair's actual ambient carriers supply all tangent and
non-tangent order comparisons along each common prefixed test stage. -/
theorem ordAgreeBelowAt_stage_of_ambient_carriers
    {n : ℕ} {X : CMfd.{0} n} (hn : 0 < n) (P Q R S : MarkedIdeal n X)
    (F : List (Set X)) (hwfP : P.IsWellFormed) (hwfQ : Q.IsWellFormed)
    (hwfR : R.IsWellFormed) (hwfS : S.IsWellFormed)
    (hsubP : P.N ⊆ R.N) (hsubQ : Q.N ⊆ S.N)
    (hrelP : LocWPEquiv { P with E := F ++ P.E } R)
    (hrelQ : LocWPEquiv { Q with E := F ++ Q.E } S)
    (hbaseP : ∀ x ∈ P.N, ∃ m, RegularAtDim (n := n) R.N x (m+1) ∧
      RegularAtDim (n := n) P.N x m)
    (hbaseQ : ∀ x ∈ Q.N, ∃ m, RegularAtDim (n := n) S.N x (m+1) ∧
      RegularAtDim (n := n) Q.N x m)
    (hdP : 1 ≤ P.d) (hd : Q.d = P.d) (hE : Q.E = P.E)
    (hL : LocWPEquiv { P with E := F ++ P.E } { Q with E := F ++ P.E })
    (hsnc : IsSNCDivisor n (F ++ P.E)) (hdim : SameCarrierDim P Q) :
    ∀ {Y : CMfd.{0} n} (T : BlowupTower X Y), IsGeoTestTower { P with E := F ++ P.E } T →
      ∀ y ∈ (geoTransformAlong P T).cosupp,
        IsNonzeroAlongAt (geoTransformAlong P T).N (geoTransformAlong P T).ideal y →
        IsNonzeroAlongAt (geoTransformAlong Q T).N (geoTransformAlong Q T).ideal y →
        OrdAgreeBelowAt (geoTransformAlong P T) (geoTransformAlong Q T) y := by
  intro Y T hT y hy hyP hyQ
  have hW := hL.wEquiv
  have hFQ : ({ Q with E := F ++ P.E } : MarkedIdeal n X) = { Q with E := F ++ Q.E } := by rw [hE]
  have hTQF : IsGeoTestTower { Q with E := F ++ Q.E } T := hFQ ▸ (hW.2 T).1.mp hT
  have hTP : IsGeoTestTower P T := isGeoTestTower_of_addE P F T hT
  have hTQ : IsGeoTestTower Q T := isGeoTestTower_of_addE Q F T hTQF
  have hwA := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hwfP T hTP
  have hwB := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hwfQ T hTQ
  have hLT := LocEquiv.geoTransformAlong hL T hT
  obtain ⟨G, hG⟩ := geoTransformAlong_addE P F T
  obtain ⟨G', hG'⟩ := geoTransformAlong_addE Q F T
  have hsncT := isSNCDivisor_geoTransformAlong (P := { P with E := F ++ P.E }) hsnc T hT
  rw [hG] at hLT hsncT
  rw [hFQ, hG'] at hLT
  have hdimT := sameCarrierDim_geoTransformAlong_of_addE F hwfP hwfQ hE hW hdim T hT
  have hyN : y ∈ (geoTransformAlong P T).N := (geoTransformAlong P T).cosupp_subset_N hy
  have hyNQ : y ∈ (geoTransformAlong Q T).N :=
    (geoTransformAlong Q T).cosupp_subset_N (hLT.cosupp_eq_base ▸ hy)
  obtain ⟨hwR, hsubR, hER, m, hmR, hmP⟩ :=
    ambient_hypersurface_along_prefixed_test P R hwfP hwfR hsubP F hrelP hbaseP T hT hyN
  obtain ⟨hwS, hsubS, hES, m', hmS, hmQ'⟩ :=
    ambient_hypersurface_along_prefixed_test Q S hwfQ hwfS hsubQ F hrelQ hbaseQ T hTQF hyNQ
  have hmQ : RegularAtDim (n := n) (geoTransformAlong Q T).N y m := (hdimT y hy m).mp hmP
  have hmm : m' = m := RegularPointDimension.eq_of_regularAtDim hmQ' hmQ
  subst m'
  rw [hG] at hER
  rw [hG'] at hES
  change (geoTransformAlong R T).E = G ++ (geoTransformAlong P T).E at hER
  have hEQG : G' ++ (geoTransformAlong Q T).E = G ++ (geoTransformAlong P T).E := hLT.E_eq
  have hESfull : (geoTransformAlong S T).E = G ++ (geoTransformAlong P T).E := by
    exact hES.trans hEQG
  have hLT' : LocWPEquiv (X := Y)
      { geoTransformAlong P T with E := G ++ (geoTransformAlong P T).E }
      { geoTransformAlong Q T with E := G ++ (geoTransformAlong P T).E } := by
    simpa only [hEQG] using hLT
  have hTR : IsTransverse n (geoTransformAlong R T).N (G ++ (geoTransformAlong P T).E) := by
    rw [← hER]
    exact hwR.isTransverse
  have hTS : IsTransverse n (geoTransformAlong S T).N (G ++ (geoTransformAlong P T).E) := by
    rw [← hESfull]
    exact hwS.isTransverse
  exact HironakaG8CaseTAmbientOrder.ordAgreeBelowAt_of_transverse_ambient_carriers
    hn { geoTransformAlong P T with E := G ++ (geoTransformAlong P T).E }
    { geoTransformAlong Q T with E := G ++ (geoTransformAlong P T).E }
    hLT' hwA.isClosedSubmanifold_N hwB.isClosedSubmanifold_N hwA.isCoherent hwB.isCoherent hsncT
    (by simpa only [d_geoTransformAlong] using hdP)
    (by simpa only [d_geoTransformAlong] using hd) hdimT hy hyP hyQ hmP hmQ
    (geoTransformAlong R T).N (geoTransformAlong S T).N hmR hmS hsubR hsubS hTR hTS

end
end Hironaka.HironakaG8CaseTAmbientStageOrder
