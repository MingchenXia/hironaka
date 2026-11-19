import Hironaka.Geometry.AlterationDominatingBaseChange

/-!
# The actual finite open of a dominating alteration base change

The actual opposite alteration's finite target open pulls back to a
nonempty actual open of the original dominant source. The component
projection is finite over that precise open, by the actual restricted
native Cartesian square and actual closed-immersion composition.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

noncomputable section

namespace Hironaka.Geometry.AlterationDominatingBaseChange

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {X Y S T : Scheme.{u}}

/-- The first actual closed-component projection is finite over the
actual inverse image of every actual finite target open of the opposite map. -/
theorem first_finite_on_preimage
    (f : X ⟶ S) (g : Y ⟶ S) (V : S.Opens) [IsFinite (g ∣_ V)]
    (j : T ⟶ pullback f g) [IsClosedImmersion j] :
    IsFinite ((j ≫ pullback.fst f g) ∣_ (f ⁻¹ᵁ V)) := by
  let m := pullback.fst f g
  let n := pullback.snd f g
  let A := f ⁻¹ᵁ V
  let B := g ⁻¹ᵁ V
  let C := m ⁻¹ᵁ A
  have hC : C = n ⁻¹ᵁ B := by
    dsimp [C, A, B, m, n]
    rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, pullback.condition]
  have H := Scheme.Hom.isPullback_resLE (IsPullback.of_hasPullback f g)
    (US := V) (UT := B) (UX := A) (UY := C) le_rfl le_rfl (by
      rw [← hC, inf_idem])
  let : IsFinite (g.resLE V B le_rfl) := by
    rw [Scheme.Hom.resLE_eq_morphismRestrict]
    infer_instance
  let : IsFinite (m ∣_ A) := by
    have hfin : IsFinite (m.resLE A C le_rfl) :=
      MorphismProperty.of_isPullback H.flip inferInstance
    simpa only [C, Scheme.Hom.resLE_eq_morphismRestrict] using hfin
  change IsFinite ((j ≫ m) ∣_ A)
  rw [morphismRestrict_comp]
  infer_instance

/-- The opposite alteration supplies the actual finite target open;
dominance supplies nonemptiness of its actual inverse image in X. -/
theorem exists_finite_open
    (f : X ⟶ S) (g : Y ⟶ S) [IsIntegral X] [IsDominant f] [hg : IsAlteration g]
    (j : T ⟶ pullback f g) [IsClosedImmersion j] :
    ∃ V : S.Opens, Nonempty V ∧ Nonempty (f ⁻¹ᵁ V) ∧ IsFinite (g ∣_ V) ∧
      IsFinite ((j ≫ pullback.fst f g) ∣_ (f ⁻¹ᵁ V)) := by
  let := hg.targetIntegral
  obtain ⟨V, hV, hfin⟩ := hg.genericallyFinite
  let := hfin
  have hηS : genericPoint S ∈ V :=
    ((genericPoint_spec S).mem_open_set_iff V.isOpen).mpr (by simpa using hV)
  have hηX : genericPoint X ∈ f ⁻¹ᵁ V := by
    change f (genericPoint X) ∈ V
    rw [genericPoint_map_of_isDominant f]
    exact hηS
  exact ⟨V, hV, ⟨⟨genericPoint X, hηX⟩⟩, hfin, first_finite_on_preimage f g V j⟩

end Hironaka.Geometry.AlterationDominatingBaseChange
