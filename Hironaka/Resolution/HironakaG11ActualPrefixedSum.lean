import Hironaka.Resolution.HironakaG8ClassStepCut
import Hironaka.Resolution.HironakaG11InvBMRebase
import Hironaka.Resolution.HironakaG8ClassStepResidual

set_option autoImplicit false

/-! Actual successor lower sums retain local equivalence after adding the
same list of original boundary members. -/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG11ActualPrefixedSum
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms HomogenizedGlueingTower
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism
  StepOneValue HironakaG11InvBMLower HironakaG11InvBMMask HironakaG11InvSameMarkSum
  HironakaG11InvBMRebase HironakaG11InvBMExceptionalTerm HironakaG11InvBMLowerTailSucc HironakaG8ClassStepCut
  HironakaG8LocalHistory HironakaG8ClassStepResidual ResolutionInvariantSpec
  HomogenizedIdealAlong

noncomputable section

/-- On an actual common successor mask, the two literal same-mark sums
remain locally weakly equivalent after adjoining any common prefix. -/
theorem actual_prefixed_successor_sums
    {n : ℕ} (hn : 0 < n) {X Y : CMfd.{0} n} {A B : MarkedIdeal n X} {k k' : ℕ}
    (hA : IsInvDomain k A) (hB : IsInvDomain k' B)
    (hmA : IsMaximalOrderAlong A.N A.ideal A.d) (hmB : IsMaximalOrderAlong B.N B.ideal B.d)
    (h : LocWPEquiv A B) (hE : A.E = B.E) (T : BlowupTower X Y)
    (hT : IsGeoTestTower (barMarked A) T) {a : Y}
    (ha : a ∈ (geoTransformAlong (barMarked A) T).cosupp) (s : ℕ)
    (hlevel : level A T a = s+1) (O : Opens Y)
    (hOA : O ≤ maskBM A (s+1) T a) (hOB : O ≤ maskBM B (s+1) T a)
    (F : List (Set O)) :
    let CA : MarkedIdeal n (CMfd.of (n := n) O) := MarkedIdeal.pullback (Subtype.val : O → Y) (contactCoeffBM A (tangentChoice A (T.proj a)).2 T)
    let CB : MarkedIdeal n (CMfd.of (n := n) O) := MarkedIdeal.pullback (Subtype.val : O → Y) (contactCoeffBM B (tangentChoice B (T.proj a)).2 T)
    let KA : MarkedIdeal n (CMfd.of (n := n) O) := excMarked n CA.N CA.E ((throughMembers A T a).map ((Subtype.val : O → Y) ⁻¹' ·)) CA.d
    let KB : MarkedIdeal n (CMfd.of (n := n) O) := excMarked n CB.N CB.E ((throughMembers B T a).map ((Subtype.val : O → Y) ⁻¹' ·)) CB.d
    LocWPEquiv (X := CMfd.of (n := n) O) {sumMarked CA KA with E := F ++ CA.E} {sumMarked CB KB with E := F ++ CA.E} := by
  have hWA := StepOneBridge.barMarked_wEquiv A hA
  have hWB := StepOneBridge.barMarked_wEquiv B hB
  have hTA : IsGeoTestTower A T := (hWA.2 T).1.mp hT
  have hTB : IsGeoTestTower B T := (h.wEquiv.2 T).1.mp hTA
  have hTJB : IsGeoTestTower (barMarked B) T := (hWB.2 T).1.mpr hTB
  have hSmA := isClosedSubmanifold_of_mem_throughMembers A hA.isWellFormed hn T hT a
  have hSmB := isClosedSubmanifold_of_mem_throughMembers B hB.isWellFormed hn T hTJB a
  have hneA := throughMembers_ne_nil A T hlevel
  have hneB : throughMembers B T a ≠ [] := by
    rw [← throughMembers_eq_of_E_eq hE T a]
    exact hneA
  have hCA : (geoTransformAlong (coeffEmptyBM A) T).ideal.IsCoherent := by
    have hw := HironakaG11InvBMStage.isWellFormed_coeffEmptyBM hA.isWellFormed
    have ht := HironakaG11InvBMStage.isGeoTestTower_coeffEmptyBM hA.isWellFormed hA.one_le_d T
      (HironakaG11InvBMStage.isGeoTestTower_emptyBoundary A T hTA)
    exact (MarkedIdealRestrictOpen.isClosedSubmanifold_N_and_isCoherent_geoTransformAlong
      hw.isClosedSubmanifold_N hw.isCoherent T ht).2
  have hCB : (geoTransformAlong (coeffEmptyBM B) T).ideal.IsCoherent := by
    have hw := HironakaG11InvBMStage.isWellFormed_coeffEmptyBM hB.isWellFormed
    have ht := HironakaG11InvBMStage.isGeoTestTower_coeffEmptyBM hB.isWellFormed hB.one_le_d T
      (HironakaG11InvBMStage.isGeoTestTower_emptyBoundary B T hTB)
    exact (MarkedIdealRestrictOpen.isClosedSubmanifold_N_and_isCoherent_geoTransformAlong
      hw.isClosedSubmanifold_N hw.isCoherent T ht).2
  have hloc := locWPEquiv_lowerIdealBM_succ hn hA hB hmA hmB h hE T hT ha s O hOA hOB
  have hprefix := locEquiv_addE rfl hloc F
  rw [pullback_lowerIdealBM_succ_eq_sumMarked A T a s O hSmA hneA hCA,
    pullback_lowerIdealBM_succ_eq_sumMarked B T a s O hSmB hneB hCB] at hprefix
  exact hprefix

end
end Hironaka.HironakaG11ActualPrefixedSum
