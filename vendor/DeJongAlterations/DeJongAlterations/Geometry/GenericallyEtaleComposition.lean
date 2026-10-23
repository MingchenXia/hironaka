import DeJongAlterations.Basic
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen

/-!
# Composition of generic etaleness on actual dense source opens

The etale source restriction is an open map. Thus the actual intersection
with the inverse image of the second dense etale open is dense, without
dominance or integrality assumptions.
-/

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace DeJongAlterations

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {X Y Z : Scheme.{u}}

namespace Geometry.GenericallyEtaleComposition

/-- The actual intersection is dense because the etale source restriction is an open map. -/
theorem dense_inter_preimage (f : X ⟶ Y) (U : X.Opens) (V : Y.Opens)
    (hU : Dense (U : Set X)) (hV : Dense (V : Set Y)) [Etale (U.ι ≫ f)] :
    Dense ((U ⊓ f ⁻¹ᵁ V : X.Opens) : Set X) := by
  have hp : Dense ((U.ι ≫ f) ⁻¹' (V : Set Y)) := hV.preimage (U.ι ≫ f).isOpenMap
  have hi : DenseRange U.ι := by
    change Dense (Set.range U.ι)
    simpa only [Scheme.Opens.range_ι] using hU
  have h := hi.dense_image U.ι.continuous hp
  have he : U.ι '' ((U.ι ≫ f) ⁻¹' (V : Set Y)) =
      ((U ⊓ f ⁻¹ᵁ V : X.Opens) : Set X) := by
    ext x
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact ⟨p.property, hp⟩
    · intro hx
      exact ⟨⟨x, hx.1⟩, hx.2, rfl⟩
  rwa [he] at h

/-- The actual restricted composite is etale on the intersection of the two source witnesses. -/
theorem etale_inter_preimage (f : X ⟶ Y) (g : Y ⟶ Z) (U : X.Opens) (V : Y.Opens)
    [Etale (U.ι ≫ f)] [Etale (V.ι ≫ g)] :
    Etale ((U ⊓ f ⁻¹ᵁ V).ι ≫ (f ≫ g)) := by
  let W := U ⊓ f ⁻¹ᵁ V
  let i := X.homOfLE (show W ≤ U from inf_le_left)
  have hi : W.ι ≫ f = i ≫ (U.ι ≫ f) := by
    rw [← Category.assoc, Scheme.homOfLE_ι]
  let : Etale (W.ι ≫ f) := by
    rw [hi]
    infer_instance
  let r := f.resLE V W (show W ≤ f ⁻¹ᵁ V from inf_le_right)
  let : Etale (r ≫ V.ι) := by
    rw [Scheme.Hom.resLE_comp_ι]
    infer_instance
  let : Etale r := Etale.of_comp r V.ι
  have h : Etale (r ≫ (V.ι ≫ g)) := inferInstance
  have hr : r ≫ (V.ι ≫ g) = W.ι ≫ (f ≫ g) := by
    rw [← Category.assoc, Scheme.Hom.resLE_comp_ι, Category.assoc]
  rw [hr] at h
  exact h

end Geometry.GenericallyEtaleComposition

/-- Native generic etaleness composes for arbitrary schemes, with its dense intersection produced. -/
theorem IsGenericallyEtale.comp {f : X ⟶ Y} {g : Y ⟶ Z}
    (hf : IsGenericallyEtale f) (hg : IsGenericallyEtale g) : IsGenericallyEtale (f ≫ g) := by
  obtain ⟨U, hU, hfU⟩ := hf
  obtain ⟨V, hV, hgV⟩ := hg
  let : Etale (U.ι ≫ f) := hfU
  let : Etale (V.ι ≫ g) := hgV
  exact ⟨U ⊓ f ⁻¹ᵁ V,
    Geometry.GenericallyEtaleComposition.dense_inter_preimage f U V hU hV,
    Geometry.GenericallyEtaleComposition.etale_inter_preimage f g U V⟩

end DeJongAlterations
