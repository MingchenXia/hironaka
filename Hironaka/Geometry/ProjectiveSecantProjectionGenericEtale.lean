import Hironaka.Geometry.ProjectiveSecantProjectionUnramifiedOpen
import Hironaka.Geometry.GenericFlatness
import Hironaka.Geometry.FiniteGenericallyEtaleOpen
import Hironaka.Geometry.AlterationComposition

/-!
# Actual generic flatness turns the same original nonempty unramified source open into genuine generic etaleness
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace Hironaka.Geometry.ProjectiveSecant

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The original finite dominant map internally produces its actual flat target open and an actual dense etale source restriction, starting from the same original nonempty unramified source open. -/
theorem genericallyEtale_of_nonempty_formallyUnramified_open
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) [IsFinite f] [IsDominant f] [LocallyOfFinitePresentation f]
    (A : X.Opens) (hA : (A : Set X).Nonempty) [FormallyUnramified (A.ι ≫ f)] :
    IsGenericallyEtale f := by
  obtain ⟨V, hV, hflat⟩ := GenericFlatness.exists_nonempty_flat_of_isIntegral f
  let : Flat (f ∣_ V) := hflat
  have hηA : genericPoint X ∈ A := (genericPoint_spec X).mem_open_set_iff A.isOpen |>.mpr
    (by simpa using hA)
  have hηV : genericPoint Y ∈ V := (genericPoint_spec Y).mem_open_set_iff V.isOpen |>.mpr
    (by simpa using hV)
  have hηpre : genericPoint X ∈ f ⁻¹ᵁ V := by
    change f (genericPoint X) ∈ V
    rw [genericPoint_map_of_isDominant f]
    exact hηV
  let W := A ⊓ f ⁻¹ᵁ V
  have hW : (W : Set X).Nonempty := ⟨genericPoint X, hηA, hηpre⟩
  have htflat : W.ι ≫ f = X.homOfLE (show W ≤ f ⁻¹ᵁ V from inf_le_right) ≫
      (f ∣_ V) ≫ V.ι := by
    rw [morphismRestrict_ι, ← Category.assoc, Scheme.homOfLE_ι]
  let : Flat (W.ι ≫ f) := by rw [htflat]; infer_instance
  have htfu : W.ι ≫ f = X.homOfLE (show W ≤ A from inf_le_left) ≫ (A.ι ≫ f) := by
    rw [← Category.assoc, Scheme.homOfLE_ι]
  let : FormallyUnramified (W.ι ≫ f) := by
    rw [htfu]
    exact MorphismProperty.comp_mem @FormallyUnramified _ _ inferInstance inferInstance
  exact ⟨W, W.isOpen.dense hW, Etale.of_formallyUnramified_of_flat (W.ι ≫ f)⟩

/-- Actual unramifiedness at one SAME original point internally produces genuine generic etaleness of the entire original finite dominant map; no flat/open-etale certificate is supplied. -/
theorem genericallyEtale_of_formallyUnramified_stalk
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) [IsFinite f] [IsDominant f] [LocallyOfFinitePresentation f]
    (x : X) (hfu : (f.stalkMap x).hom.FormallyUnramified) : IsGenericallyEtale f := by
  obtain ⟨A, hxA, hA⟩ := exists_formallyUnramified_open_of_stalk f x hfu
  let := hA
  exact genericallyEtale_of_nonempty_formallyUnramified_open f A ⟨x, hxA⟩

end Hironaka.Geometry.ProjectiveSecant
