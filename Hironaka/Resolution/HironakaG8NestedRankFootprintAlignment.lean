import Hironaka.Resolution.HironakaG8OrderedFootprintTraces

set_option autoImplicit false
open Set TopologicalSpace Classical
open scoped Manifold ContDiff
namespace Hironaka.HironakaG8NestedRankFootprintAlignment
open BlowupTowers BlowupTowerTransforms MaxLocusLocal
  HironakaG8OccupiedSlotComparison HironakaG8OrderedFootprintTraces

variable {n : ℕ} {X A B : CMfd.{0} n}

/-- Equality of the ambient ordered traces is the exact occupied list
equality on the literal restricted larger tower after base transport. -/
theorem nested_occupied_footprints_eq_of_ambient_traces
    {U V : Opens X}
    (L : BlowupTower (CMfd.of (n := n) U) A)
    (R : BlowupTower (CMfd.of (n := n) V) B)
    (φ : CMfd.of (n := n) U ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
      CMfd.of (n := n) (nestedOpens V U))
    (hφ : ∀ x : U, (φ x).val.val = x.val)
    (h : (occupiedFootprints L).map (fun a => (Subtype.val : U → X) '' a) =
      ((occupiedFootprints R).map (fun a => (Subtype.val : V → X) '' a)).filterMap
        (fun a => if (a ∩ (U : Set X)).Nonempty then some (a ∩ (U : Set X)) else none)) :
    occupiedFootprints L = (occupiedFootprints (restrict (nestedOpens V U) R)).map (φ ⁻¹' ·) := by
  let liftU : Set U → Set X := fun a => (Subtype.val : U → X) '' a
  let liftV : Set V → Set X := fun a => (Subtype.val : V → X) '' a
  have hInj : Function.Injective liftU := Set.image_injective.mpr Subtype.val_injective
  apply List.map_injective_iff.mpr hInj
  rw [h,occupiedFootprints_restrict_eq_filterMap]
  let O := nestedOpens V U
  let trace (a : Set V) : Set U := φ ⁻¹' ((Subtype.val : O → V) ⁻¹' a)
  have hTrace (a : Set V) : liftU (trace a) = liftV a ∩ (U : Set X) := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      exact ⟨⟨(φ y).val,hy,hφ y⟩,y.property⟩
    · rintro ⟨⟨z,hz,hx⟩,hxU⟩
      let y : U := ⟨x,hxU⟩
      have hzEq : (φ y).val = z := Subtype.ext ((hφ y).trans hx.symm)
      refine ⟨y,?_,rfl⟩
      change (φ y).val ∈ a
      rwa [hzEq]
  have hQual (a : Set V) : (a ∩ (O : Set V)).Nonempty ↔ (liftV a ∩ (U : Set X)).Nonempty := by
    have hIm : (Subtype.val : V → X) '' (a ∩ (O : Set V)) = liftV a ∩ (U : Set X) := by
      change (Subtype.val : V → X) '' (a ∩ ((Subtype.val : V → X) ⁻¹' (U : Set X))) = _
      exact Set.image_inter_preimage (Subtype.val : V → X) a (U : Set X)
    rw [← hIm]
    exact Set.image_nonempty.symm
  generalize occupiedFootprints R = parts
  induction parts with
  | nil => rfl
  | cons a l ih =>
    by_cases ha : (a ∩ (nestedOpens V U : Set V)).Nonempty
    · have hb : ((Subtype.val : V → X) '' a ∩ (U : Set X)).Nonempty := (hQual a).mp ha
      simp only [List.map_cons,List.filterMap_cons,if_pos ha,if_pos hb]
      exact congrArg₂ List.cons (hTrace a).symm ih
    · have hb : ¬ ((Subtype.val : V → X) '' a ∩ (U : Set X)).Nonempty :=
        mt (hQual a).mpr ha
      simpa only [List.map_cons,List.filterMap_cons,if_neg ha,if_neg hb] using ih

end Hironaka.HironakaG8NestedRankFootprintAlignment
