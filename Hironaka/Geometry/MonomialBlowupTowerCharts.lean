import Hironaka.Geometry.MonomialBlowupTowerChartRange

/-! Actual successor chart witnesses assembled from separately checked native maps and ranges. -/

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace Hironaka.Geometry.MonomialBlowupTowerCharts

open Algebra.NodeBlowupChart Algebra.MonomialBlowupIteration
open MonomialBlowupTower MonomialBlowupTowerBase BlowupGluing

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {A : Type u} [CommRing A] [IsDomain A]

/-- The successor cover is constructed on the actual next global blowup. -/
theorem nextCharts {l : List A} {n : ℕ} {P t : A} (b : List A)
    (S : ChartData l n P (t * b.prod))
    (hprefix : (l.take (n + 1)).prod = P * t)
    (ht : t ≠ 0) (hb : b.prod ≠ 0) (htmem : t ∈ l) :
    Nonempty (ChartData l (n + 1) (P * t) b.prod) := by
  refine ⟨?_⟩
  let : Fact (t ≠ 0) := ⟨ht⟩
  let : Fact (b.prod ≠ 0) := ⟨hb⟩
  let D := stageCenter (originalCenter l) n
  let oldInclusion := StepContext.oldInclusion S hprefix
  let freshInclusion := StepContext.freshInclusion S hprefix
  let nextInclusion := StepContext.nextInclusion S hprefix
  have hold := StepContext.oldInclusion_structure S hprefix
  have hfresh := StepContext.freshInclusion_structure S hprefix
  have hnext := StepContext.nextInclusion_structure S hprefix
  have hcovernext := StepContext.covers S hprefix
  refine {
    I := Option S.I
    factor := fun i ↦ i.elim t S.factor
    factor_mem := ?_
    factor_ne_zero := ?_
    scale := fun i ↦ i.elim P S.scale
    scale_ne_zero := ?_
    divides_prefix := ?_
    ringMap := fun i ↦ by
      cases i with
      | none => exact (uChartOriginalMap t b.prod).comp S.continuationRingMap
      | some i => exact S.ringMap i
    ringMap_u := ?_
    inclusion := fun i ↦ by
      cases i with
      | none => exact freshInclusion
      | some i => exact oldInclusion i
    inclusion_open := ?_
    inclusion_structure := ?_
    prefix_ne_zero := mul_ne_zero S.prefix_ne_zero ht
    remaining_ne_zero := hb
    continuationRingMap := (continuationMap t b.prod).comp S.continuationRingMap
    continuationRingMap_u := ?_
    continuationInclusion := nextInclusion
    continuation_open := ?_
    continuation_structure := ?_
    covers := ?_ }
  · intro i
    cases i with
    | none => exact htmem
    | some i => exact S.factor_mem i
  · intro i
    cases i with
    | none => exact ht
    | some i => exact S.factor_ne_zero i
  · intro i
    cases i with
    | none => exact S.prefix_ne_zero
    | some i => exact S.scale_ne_zero i
  · intro i
    cases i with
    | none => exact dvd_refl _
    | some i => exact dvd_mul_of_dvd_left (S.divides_prefix i) t
  · intro i
    cases i with
    | none =>
      change uChartOriginalMap t b.prod (S.continuationRingMap (coordinate l.prod 0)) =
        algebraMap A (Node A t) P * coordinate t 0
      rw [S.continuationRingMap_u, map_mul, AlgHom.commutes, uChartOriginalMap_coordinate0]
    | some i => exact S.ringMap_u i
  · intro i
    cases i <;> dsimp only [freshInclusion, oldInclusion] <;> infer_instance
  · intro i
    cases i with
    | none =>
      change freshInclusion ≫ (blowupStructure D ≫ (tower l n).hom) = _
      rw [← Category.assoc, hfresh, Category.assoc, S.continuation_structure, ← Spec.map_comp]
      rfl
    | some i =>
      change oldInclusion i ≫ (blowupStructure D ≫ (tower l n).hom) = _
      rw [← Category.assoc, hold, S.inclusion_structure]
  · simp only [AlgHom.comp_apply, S.continuationRingMap_u, map_mul,
      AlgHom.commutes, continuationMap_coordinate0, mul_assoc]
  · dsimp only [nextInclusion]
    infer_instance
  · change nextInclusion ≫ (blowupStructure D ≫ (tower l n).hom) = _
    rw [← Category.assoc, hnext, Category.assoc, S.continuation_structure, ← Spec.map_comp]
    rfl
  · intro y
    rcases hcovernext y with ⟨i, hi⟩ | hf | hn
    · exact Or.inl ⟨some i, hi⟩
    · exact Or.inl ⟨none, hf⟩
    · exact Or.inr hn

end Hironaka.Geometry.MonomialBlowupTowerCharts
