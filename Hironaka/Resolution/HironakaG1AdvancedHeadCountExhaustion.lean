import Hironaka.Resolution.HironakaG1LaterAdvancedHeadTerminalExample
import Hironaka.Resolution.HironakaG1LaterMixedUpperBornTrace
import Hironaka.Resolution.HironakaG8PowerLowerMarks

/-! # Retained upper-head counts on the concrete advanced-head canonical history -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace

namespace Hironaka.HironakaG1AdvancedHeadCountExhaustion
noncomputable section

open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms BlowupTowerSplit
  MarkedIdeals MarkedIdeals.MarkedIdeal ResolutionInvariantSpec CanonicalCentres
  StepOneValue StepOneValueMasked StepOneRegime NonmonomialOrderLocal
  HironakaActualOpenZeroSectionDifferentials HironakaG1ProperCarrierNormalDerivativeTrace
  HironakaG1PositiveNormalJointExample HironakaG1LaterPositiveNormalExample
  HironakaG1LaterAdvancedHeadExample HironakaG1LaterAdvancedHeadCanonicalExample
  HironakaG1LaterAdvancedHeadNumericalExample HironakaG1LaterAdvancedHeadNativeValueExample
  HironakaG1LaterAdvancedHeadTerminalExample HironakaG1LaterPositiveBranchOrder
  HironakaG1ActualLaterSuccessorRead HironakaG8PowerLowerMarks
  HironakaG1LaterMixedUpperBornTrace HironakaG1InitialPositiveGeneralRead HironakaG1LaterPositiveStratumCentres

private abbrev U : Opens (ComplexModel 2) := ⊤
private abbrev X := CMfd.of (n := 3) (productOpen U)
private abbrev old (i : Fin 2) : Set U := {x | x.val i = 0}
private abbrev A : MarkedIdeal 2 U := {sourceRecord with E := [old 0, old 1]}
private abbrev M : MarkedIdeal 3 X := properNormalMarked A
private abbrev F {Z : CMfd.{0} 3} : BlowupTower X Z → Z → ℕ ×ₗ WithTop (ValTy 2) := Seq.StepOneValueMasked.stepOneInvM (invFamily (by decide : 0 < 3) 2) M

set_option maxHeartbeats 1700000 in
/-- The occupied advanced head has a genuinely nonzero retained count.
The whole actual first endpoint cosupport is the singleton that realizes it. -/
theorem advanced_first_stage_every_survivor_retains_one :
    ∀ y ∈ (geoTransformAlong M B).cosupp,
      y = q ∧ regimeRun (stepRegime M 1) B y = 0 ∧
        upperHeadNonOriginalBoundaryCount A B 0 y = 1 := by
  intro y hy
  have hyq : y = q := mem_singleton_iff.mp (joint_advanced_head_endpoint_cosupport ▸ hy)
  subst y
  have hDomain : IsInvDomain 2 A := HironakaG1LaterAdvancedHeadNativeExample.Q_domain
  have hCan : IsCanonical M F B := joint_advanced_head_isCanonical _
  have hLevel : level M B q = 1 := joint_added_boundary_upper_regime_advances.2.1
  have hReg : regimeRun (stepRegime M 1) B q = 0 := by
    have h : regimeRun (stepRegime M (level M B q)) B q = 0 :=
      joint_added_boundary_upper_regime_advances.2.2
    rw [hLevel] at h
    exact h
  have hOrder : LaterPositiveOrderAt A B q 0 1 := by
    unfold LaterPositiveOrderAt
    intro r H S p O X' Y' L V z hz
    have h := (original_upper_positive_lower_raw_mark (s := 0) A hDomain B hCan q hy
      hLevel joint_added_boundary_survives_nonspecial.2).2 z hz
    have hMark : L.d = 1 := by
      change (lowerMarkedM M 1 H p).d = 1
      rw [lowerMarkedM_succ_mark]
      decide
    exact h.trans hMark
  obtain ⟨read, hReadOrder⟩ := exists_laterPositiveRead A B q hDomain hCan hy hLevel
    joint_added_boundary_survives_nonspecial.2 1 (by decide) hOrder
  have hRaw : F B q = toLex (1, (positiveSuccessorRead read.order read.companion : WithTop (ValTy 2))) :=
    read.raw_upper
  rw [hReadOrder] at hRaw
  have hRead := joint_advanced_head_exact_upper_value.symm.trans hRaw
  have hLetter := WithTop.coe_inj.mp
    (congrArg (fun w : ℕ ×ₗ WithTop (ValTy 2) => (ofLex w).2) hRead)
  have hComp := WithTop.coe_inj.mp
    (Sum.inr.inj (congrArg (fun w : ValTy 2 => ofLex ((ofLex w).2)) hLetter))
  have hOne : (ofLex read.companion).1 = 1 :=
    (congrArg (fun w : ℕ ×ₗ WithTop (ValTy 1) => (ofLex w).1) hComp).symm
  have hCount := laterPositiveRead_companion_level_eq_upperHeadNonOriginal A B hDomain hCan q hy
    hLevel joint_added_boundary_survives_nonspecial.2 read
  exact ⟨rfl, hReg, hCount.symm.trans hOne⟩

set_option maxHeartbeats 1000000 in
/-- The actual second occupied blowup in this concrete canonical history
has empty cosupport. Thus the stage with a nonzero retained count has
only one surviving point, and the next stage has none. -/
theorem advanced_two_occupied_stages_exhaust_retained_competitors :
    (positiveLevelStratum A B 0 = {q} ∧ upperHeadNonOriginalBoundaryCount A B 0 q = 1) ∧
      ∃ (W : CMfd.{0} 3) (ρ : W → Y) (hρ : IsBlowupAlong 3 ({q} : Set Y) ρ),
        let H : BlowupTower X W := .step B {q} ρ hρ
        H.length = 2 ∧ IsCanonical M F H ∧
          ∀ s, positiveLevelStratum A H s = ∅ := by
  have hq := joint_added_boundary_survives_nonspecial.1
  have hLevel : level M B q = 1 := joint_added_boundary_upper_regime_advances.2.1
  refine ⟨⟨?_, (advanced_first_stage_every_survivor_retains_one q hq).2.2⟩, ?_⟩
  · ext y
    constructor
    · intro hy
      exact mem_singleton_iff.mpr (advanced_first_stage_every_survivor_retains_one y hy.1).1
    · intro hy
      rw [mem_singleton_iff.mp hy]
      exact ⟨hq, hLevel⟩
  obtain ⟨W, ρ, hρ, _, hCan, _, _, hEmpty⟩ := joint_advanced_head_padded_complete_history
  refine ⟨W, ρ, hρ, rfl, hCan, fun s => ?_⟩
  apply Set.eq_empty_of_forall_notMem
  intro y hy
  have hm := hy.1
  change y ∈ (geoTransformAlong M (.step B {q} ρ hρ)).cosupp at hm
  have hm' : y ∈ (∅ : Set W) := (show (geoTransformAlong M (.step B {q} ρ hρ)).cosupp = ∅ from hEmpty) ▸ hm
  exact hm'

end
end Hironaka.HironakaG1AdvancedHeadCountExhaustion
