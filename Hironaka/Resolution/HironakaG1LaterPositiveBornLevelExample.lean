import Hironaka.Resolution.HironakaG1LaterPositiveSelectedExample
import Hironaka.Resolution.HironakaG1InitialPositiveSpecialRecoding

/-! The born divisor in the actual positive lower record after the first point blowup. -/

set_option autoImplicit false

open Set TopologicalSpace
open scoped Topology

namespace Hironaka.HironakaG1LaterPositiveBornLevelExample

noncomputable section

open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms
  BlowupFlatCoordinates BlowupMonomialCharts BlowupStrictSubmanifold
  MarkedIdeals MarkedIdeals.MarkedIdeal NormalCrossings ResolutionInvariantSpec
  StepOneValue StepOneValueMasked StepOneLowerDomain BoundaryCount InvDomainMemberRestriction
  HironakaActualOpenZeroSectionDifferentials HironakaG1ProperCarrierNormalContact
  HironakaG1ProperCarrierNormalDerivativeTrace HironakaActualNativeSectionInitialBar
  HironakaRelativeNormalIdeal StepOneRegime
  HironakaG1PositiveNormalNonspecialExample HironakaG1PositiveNormalJointExample
  HironakaG1LaterPositiveNormalExample HironakaG1LaterPositiveSelectedExample
  HironakaG1InitialPositiveSpecialRecoding

private abbrev U : Opens (ComplexModel 2) := ⊤
private abbrev X := CMfd.of (n := 3) (productOpen U)
private abbrev p : X := zeroSection U ⟨0, mem_univ _⟩
private abbrev C : Set X := {p}
private abbrev D : Set X :=
  projection U ⁻¹' ((Subtype.val : U → ComplexModel 2) ⁻¹' firstCoordinateDivisor)
private abbrev P : MarkedIdeal 3 X := properNormalMarked sourceRecord
private abbrev O := maskA P B q
private abbrev L := lowerMarkedM P 1 B q
private abbrev D' := geoStrictTransform π C D
private abbrev F : Set Y := π ⁻¹' C

private theorem old_ne_born : D' ≠ F := by
  intro h
  let v := EuclideanSpace.single (1 : Fin 3) (1 : ℂ)
  let z := yChart.invFun v
  have hz : z ∈ yChart.source := yChart.toPartialEquiv.map_target (chart_all v)
  have hcoord : yChart.toFun z = v := yChart.toPartialEquiv.right_inv (chart_all v)
  have hproj : (π z).val = monomial 0 (1 : Fin 3) v := by rw [chart_projection z hz, hcoord]
  have hzD : π z ∈ D := by
    change (π z).val (0 : Fin 3) = 0
    rw [hproj, monomial_apply]
    simp [v]
  have hzC : π z ∉ C := by
    intro hp
    have h0 : p.val = 0 := map_zero (tangentInclusion 2 1)
    have heq := congrArg (fun x : X => x.val (1 : Fin 3)) (mem_singleton_iff.mp hp)
    change (π z).val (1 : Fin 3) = p.val (1 : Fin 3) at heq
    rw [hproj, h0, monomial_apply] at heq
    simp [v] at heq
  have hzD' : z ∈ D' := subset_closure (show π z ∈ D \ C from ⟨hzD, hzC⟩)
  exact hzC ((h ▸ hzD') : z ∈ F)

private theorem filtered_boundary (D₀ F₀ : Set Y) (h : D₀ ≠ F₀) (hq : q ∈ D₀) :
    (((List.finRange [D₀, F₀].length).filter fun i =>
      i ∉ membersThrough [D₀, F₀] [D₀] q).map [D₀, F₀].get) = [F₀] := by
  classical
  have hZero : (0 : Fin 2) ∈ membersThrough [D₀, F₀] [D₀] q :=
    mem_membersThrough.mpr (by simpa using hq)
  have hOne : (1 : Fin 2) ∉ membersThrough [D₀, F₀] [D₀] q := by
    rw [mem_membersThrough]
    simp [Ne.symm h]
  change (List.finRange 2 |>.filter (fun i => i ∉ membersThrough [D₀, F₀] [D₀] q) |>.map [D₀, F₀].get) = _
  rw [show List.finRange 2 = [(0 : Fin 2), 1] from by decide]
  simp [hZero, hOne]

/-- The literal selected lower record on the positive mask keeps exactly the
born exceptional divisor, pulled back to that mask. -/
theorem joint_first_blowup_selected_boundary :
    L.E = [(Subtype.val : O → Y) ⁻¹' F] := by
  classical
  let A := geoTransformAlong (barMarked P) B
  have hA : A.E = [D', F] := rfl
  have hOrig : origMembers P B = [D'] := rfl
  have hqD : q ∈ D' := joint_first_point_blowup_positive_normal_contact.2.2.2.2.2.1
  change List.map (fun H => (Subtype.val : O → Y) ⁻¹' H)
    (memberRestrict A (membersThrough A.E (origMembers P B) q)).E = _
  rw [memberRestrict_E]
  have hRetained := filtered_boundary D' F old_ne_born hqD
  rw [← hA, ← hOrig] at hRetained
  rw [hRetained]
  rfl

/-- The later survivor belongs to its actual positive mask, and the selected
lower record has level one at the anchor with empty lower history. -/
theorem joint_first_blowup_selected_anchor_level :
    ∃ hq : q ∈ O,
      level L (BlowupTower.refl (X := CMfd.of (n := 3) O)) (⟨q, hq⟩ : O) = 1 := by
  have hqO : q ∈ O := joint_first_blowup_masked_selected_normal_tangent.1.1
  refine ⟨hqO, ?_⟩
  have hqF : q ∈ F := by
    change π q ∈ C
    rw [joint_first_point_blowup_positive_normal_contact.2.2.2.1]
    exact mem_singleton _
  have hOrig : origMembers L (BlowupTower.refl (X := CMfd.of (n := 3) O)) = L.E :=
    List.take_length
  unfold level
  rw [hOrig, joint_first_blowup_selected_boundary]
  classical
  unfold boundaryCount
  rw [Finset.filter_true_of_mem]
  · simp
  · intro i _
    have hi : i.val = 0 := Nat.lt_one_iff.mp i.isLt
    simpa [List.get_eq_getElem, hi] using hqF

set_option maxHeartbeats 230000 in
set_option backward.isDefEq.respectTransparency false in
/-- With the same upper record and positive level one, the selected lower
anchor has level zero at the empty upper head and level one after the point
blowup. The actual inner Step One first component therefore changes too. -/
theorem joint_positive_inner_first_component_changes {k : ℕ} {Λ : Type} [LinearOrder Λ]
    (R : ResolutionInvariantSeq.ResolutionInvariant.{0, 0} 3 k Λ) :
    let T : BlowupTower X X := .refl
    let O₀ := maskA P T p
    let L₀ := lowerMarkedM P 1 T p
    let I₀ := BlowupTower.refl (X := CMfd.of (n := 3) O₀)
    let I₁ := BlowupTower.refl (X := CMfd.of (n := 3) O)
    ∃ (hp : p ∈ O₀) (hq : q ∈ O),
      level P T p = 1 ∧ level P B q = 1 ∧
        (ofLex (Seq.StepOneValueMasked.stepOneInvM R L₀ I₀ ⟨p, hp⟩)).1 = 0 ∧
        (ofLex (Seq.StepOneValueMasked.stepOneInvM R L I₁ ⟨q, hq⟩)).1 = 1 := by
  intro T O₀ L₀ I₀ I₁
  obtain ⟨_, _, pO, _, _, _, hpO, _, hpCos, _, hpLevel, _, _, _, _, _, _⟩ :=
    joint_positive_nonspecial_first_entries
  have hpValue : pO.val = p := hpO
  have hp : p ∈ O₀ := by
    rw [← hpValue]
    exact pO.property
  obtain ⟨hq, hOne⟩ := joint_first_blowup_selected_anchor_level
  have hZero : level L₀ I₀ (⟨p, hp⟩ : O₀) = 0 :=
    (original_initial_masked_positive_special_iff sourceRecord sourceRecord_domain p hpCos
      (s := 0) hpLevel ⟨p, hp⟩ rfl).1
  refine ⟨hp, hq, hpLevel, q_level, ?_, ?_⟩
  · rw [Seq.StepOneValueMasked.stepOneInvL_fst]
    exact hZero
  · rw [Seq.StepOneValueMasked.stepOneInvL_fst]
    exact hOne

/-- The last upper step in the example belongs to the same positive
nonspecial run. The canonical upper run still starts at the initial head. -/
theorem joint_first_blowup_upper_regime_run :
    regimeRun (stepRegime P (level P B q)) B q = 1 := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hpLevel, _, hpNS, _, _, _, _⟩ :=
    joint_positive_nonspecial_first_entries
  let T : BlowupTower X X := .refl
  have hq : π q = p := joint_first_point_blowup_positive_normal_contact.2.2.2.1
  have hpRegime : stepRegime P 1 T (π q) := by
    rw [hq]
    exact ⟨hpLevel, hpNS⟩
  rw [q_level]
  change regimeRun (stepRegime P 1) (.step T C π hπ) q = 1
  rw [regimeRun_step_of _ T C π hπ hpRegime, regimeRun_refl]

end
end Hironaka.HironakaG1LaterPositiveBornLevelExample
