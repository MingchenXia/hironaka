import Hironaka.Resolution.HironakaSharpActualChronologicalDistinctDefect

set_option autoImplicit false

/-! Actual whole relative strict steps cannot increase the genuine quotient
count of distinct proper residual germs. Complete source-first chapter:
`hironaka-g4-distinct-residual-count-transform.tex`. -/

open Set Filter Classical
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaG4DistinctResidualCountTransform

noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  HironakaSharpActualChronologicalDistinctDefect
  HironakaSharpActualChronologicalStrictStep HironakaSharpActualFiniteChronologicalHistory
  HironakaSharpOriginalFirstMemberRelativeStrict RelativePrincipalizationSpan
  RestrictedIdealExtension RestrictedIdealQuotient InvertibleIdealQuotient

variable {n m : ℕ} {X Y Z : CMfd.{u} n}

private theorem pullback_mem_congr {I J : GermIdeal n X} (π : Y → X) (z : Y)
    (h : ∀ a, I.mem (π z) a ↔ J.mem (π z) a) (g : Y → ℂ) :
    (GermIdeal.pullback (m := n) π I).mem z g ↔
      (GermIdeal.pullback (m := n) π J).mem z g := by
  rw [GermIdeal.mem_pullback_iff, GermIdeal.mem_pullback_iff]
  constructor
  · exact IsInSpanAt.mono fun _ ⟨a, ha, heq⟩ => ⟨a, (h a).mp ha, heq⟩
  · exact IsInSpanAt.mono fun _ ⟨a, ha, heq⟩ => ⟨a, (h a).mpr ha, heq⟩

private theorem strict_mem_congr (N C : Set X) (π : Y → X) (z : Y)
    {I J : GermIdeal n X} (h : ∀ a, I.mem (π z) a ↔ J.mem (π z) a)
    (g : Y → ℂ) :
    (nextRelativeStrict N I C π).mem z g ↔ (nextRelativeStrict N J C π).mem z g := by
  constructor
  · rintro ⟨k, hg, hcolon⟩
    refine ⟨k, hg, fun a ha => ?_⟩
    obtain ⟨hahol, hspan⟩ := hcolon a ha
    exact ⟨hahol, IsInSpanOnAt.mono (fun b hb => (pullback_mem_congr π z h b).mp hb) hspan⟩
  · rintro ⟨k, hg, hcolon⟩
    refine ⟨k, hg, fun a ha => ?_⟩
    obtain ⟨hahol, hspan⟩ := hcolon a ha
    exact ⟨hahol, IsInSpanOnAt.mono (fun b hb => (pullback_mem_congr π z h b).mpr hb) hspan⟩

private theorem strict_one_mem_of_one_mem (N C : Set X) (π : Y → X) (z : Y)
    {I : GermIdeal n X} (h : I.mem (π z) (1 : X → ℂ)) :
    (nextRelativeStrict N I C π).mem z (1 : Y → ℂ) := by
  have hOne : (GermIdeal.pullback (m := n) π I).mem z (1 : Y → ℂ) :=
    GermIdeal.mem_pullback_iff.mpr
      (isInSpanAt_self ⟨(1 : X → ℂ), h, rfl⟩ (holomorphicAt_const 1))
  refine ⟨0, holomorphicAt_const 1, fun a ha => ?_⟩
  have haHol : HolomorphicAt n a z := ha
  refine ⟨haHol.mul (holomorphicAt_const 1), 1, (fun _ => (1 : Y → ℂ)),
    (fun _ => a), (fun _ => hOne), (fun _ => haHol), ?_⟩
  exact Eventually.of_forall fun _ _ => by simp

/-- The true quotient count cannot increase under the SAME actual whole
relative strict construction; no order, principal or future-state premise. -/
theorem actual_distinct_proper_count_nextRelativeStrict_le (N C : Set X)
    (π : Y → X) (F : Fin m → GermIdeal n X) (z : Y) :
    actualDistinctProperCount (fun i => nextRelativeStrict N (F i) C π) z ≤
      actualDistinctProperCount F (π z) := by
  let F' := fun i => nextRelativeStrict N (F i) C π
  have hrel : ∀ i j, (actualIdealGermSetoid F (π z)).r i j →
      (actualIdealGermSetoid F' z).r i j := by
    intro i j hij g
    exact strict_mem_congr N C π z hij g
  have hsub : actualProperPositions F' z ⊆ actualProperPositions F (π z) := by
    intro i hi
    simp only [actualProperPositions, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    exact fun hunit => hi (strict_one_mem_of_one_mem N C π z hunit)
  let f : Quotient (actualIdealGermSetoid F (π z)) → Quotient (actualIdealGermSetoid F' z) :=
    Quotient.map id hrel
  let Q := (actualProperPositions F (π z)).image (Quotient.mk (actualIdealGermSetoid F (π z)))
  have himg : (actualProperPositions F' z).image (Quotient.mk (actualIdealGermSetoid F' z)) ⊆
      Q.image f := by
    intro q hq
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hq
    exact Finset.mem_image.mpr ⟨Quotient.mk (actualIdealGermSetoid F (π z)) i,
      Finset.mem_image.mpr ⟨i, hsub hi, rfl⟩, rfl⟩
  exact (Finset.card_le_card himg).trans Finset.card_image_le

/-- Every original chronological position is transformed together, with the
native independently established common carrier; the family is never reset. -/
theorem original_chronological_distinct_count_step_le (W : Set X) (E : List (Set X))
    (T : BlowupTower X Y) {C : Set Y} {π : Z → Y} (hπ : IsBlowupAlong n C π) (z : Z) :
    actualDistinctProperCount (fun i : Fin E.length =>
      (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) (.step T C π hπ)).ideal) z ≤
      actualDistinctProperCount (fun i : Fin E.length =>
        (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal) (π z) := by
  let N := (geoTransformAlong (geometricTemplate W []) T).N
  let F := fun i : Fin E.length =>
    (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal
  have hN (i : Fin E.length) :
      (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).N = N :=
    (chronologicalMarked_geometric_fields (originalRelativeMemberMarked W (E.get i)) T).1
  have hFamily : (fun i : Fin E.length =>
      (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) (.step T C π hπ)).ideal) =
      (fun i => nextRelativeStrict N (F i) C π) := by
    funext i
    change nextRelativeStrict _ _ C π = _
    rw [hN i]
  rw [hFamily]
  exact actual_distinct_proper_count_nextRelativeStrict_le N C π F z

end

end Hironaka.HironakaG4DistinctResidualCountTransform
