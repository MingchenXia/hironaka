import Hironaka.Resolution.HironakaG11ResidualBirthFullTrace
import Hironaka.Invariant.MemberInterTowerAlong

set_option autoImplicit false

/-! Every original member retained at an endpoint has a smooth literal
source member and smooth strict image at any fixed birth in the same history. -/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG11RetainedBirthSources
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupStrictSubmanifold HomogenizedGlueingTower MemberInterLocusAlong
  MemberInterTowerAlong MarkedIdeals MarkedIdeals.MarkedIdeal NormalCrossings
  HironakaG11InvBMLower StepOneValue

/-- The source and birth-stage strict images of every original member are
literal full-boundary members, hence smooth, independently of the anchor. -/
theorem retained_members_have_smooth_birth_sources
    {n : ℕ} (hn : 0 < n) {X Y₀ Y₁ Y : CMfd.{0} n} (A : MarkedIdeal n X)
    (hA : A.IsWellFormed) (P : BlowupTower X Y₀) (C : Set Y₀) (π : Y₁ → Y₀)
    (hπ : IsBlowupAlong n C π) (Q : BlowupTower Y₁ Y)
    (hT : IsGeoTestTower A ((BlowupTower.step P C π hπ).append Q)) (a : Y) :
    ∀ K ∈ throughMembers A ((BlowupTower.step P C π hπ).append Q) a,
      ∃ H ∈ (geoTransformAlong A P).E, IsClosedSubmanifold n H ∧
        IsClosedSubmanifold n (geoStrictTransform π C H) ∧
        K = strictAlong Q (geoStrictTransform π C H) := by
  have hStep : IsGeoTestTower A (BlowupTower.step P C π hπ) :=
    (isGeoTestTower_append_iff A (BlowupTower.step P C π hπ) Q).mp hT |>.1
  have hPA : IsGeoTestTower A P := (isGeoTestTower_step_iff A P C π hπ).mp hStep |>.1
  have hwP := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hA P hPA
  have hwStep := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hA (BlowupTower.step P C π hπ) hStep
  intro K hK
  have hOrig := (mem_throughMembers.mp hK).1
  rw [origMembers_eq] at hOrig
  obtain ⟨K₀,hK₀,hK⟩ := List.mem_map.mp hOrig
  obtain ⟨i,hi⟩ := List.get_of_mem hK₀
  let j : Fin (geoTransformAlong A P).E.length :=
    Fin.castLE (length_E_le_length_E_geoTransformAlong A P) i
  have hj : (geoTransformAlong A P).E.get j = strictAlong P K₀ := by
    rw [get_E_geoTransformAlong A P i,hi]
  have hmem : strictAlong P K₀ ∈ (geoTransformAlong A P).E := hj ▸ List.get_mem _ j
  have hmemStep : geoStrictTransform π C (strictAlong P K₀) ∈
      (geoTransformAlong A (BlowupTower.step P C π hπ)).E := by
    change geoStrictTransform π C (strictAlong P K₀) ∈
      (geoTransformAlong A P).E.map (geoStrictTransform π C) ++ [π ⁻¹' C]
    exact List.mem_append_left _ (List.mem_map.mpr ⟨_,hmem,rfl⟩)
  have hH := MonomialPart.isClosedSubmanifold_get hn hwP.isSNCDivisor j
  rw [hj] at hH
  obtain ⟨l,hl⟩ := List.get_of_mem hmemStep
  have hKsm := MonomialPart.isClosedSubmanifold_get hn hwStep.isSNCDivisor l
  rw [hl] at hKsm
  refine ⟨strictAlong P K₀,hmem,hH,hKsm,?_⟩
  rw [← hK,strictAlong_append]
  rfl

end Hironaka.HironakaG11RetainedBirthSources
