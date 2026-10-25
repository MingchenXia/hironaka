import DeJongAlterations.Geometry.CurveBoundaryBasic

/-!
# The exact reduced boundary of an actual open compactification

The closed support is constructed as the complement of the actual image of
the boundary-free source open. Both the prescribed inverse image and the
whole complement of the source appear in its exact support identity.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace DeJongAlterations.Geometry.CurveBoundary

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {S X C : Scheme.{u}}

/-- The actual closed complement of the boundary-free source open. -/
def extendedClosed (a : S ⟶ X) (i : S ⟶ C) [IsOpenImmersion i]
    (Z : Closeds X) : Closeds C :=
  (i ''ᵁ (Z.preimage a.continuous).compl).compl

/-- The actual reduced induced boundary, with no supplied ideal or support comparison. -/
def extendedBoundary (a : S ⟶ X) (i : S ⟶ C) [IsOpenImmersion i]
    (Z : Closeds X) : C.IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal (extendedClosed a i Z)

/-- The constructed closed support is exactly the prescribed inverse image
in the source, together with the entire compactification complement. -/
theorem extendedClosed_coe (a : S ⟶ X) (i : S ⟶ C) [IsOpenImmersion i]
    (Z : Closeds X) :
    (extendedClosed a i Z : Set C) = i '' (a ⁻¹' (Z : Set X)) ∪ (Set.range i)ᶜ := by
  change (i '' (a ⁻¹' (Z : Set X))ᶜ)ᶜ = _
  ext x
  constructor
  · intro hx
    by_cases hr : x ∈ Set.range i
    · obtain ⟨y, rfl⟩ := hr
      left
      refine ⟨y, ?_, rfl⟩
      by_contra hy
      exact hx ⟨y, hy, rfl⟩
    · exact Or.inr hr
  · rintro (⟨y, hy, rfl⟩ | hx) ⟨z, hz, hzx⟩
    · exact hz (i.isEmbedding.injective hzx ▸ hy)
    · exact hx ⟨z, hzx⟩

/-- The full native vanishing ideal has exactly the required boundary support. -/
theorem extendedBoundary_support (a : S ⟶ X) (i : S ⟶ C) [IsOpenImmersion i]
    (Z : Closeds X) :
    ((extendedBoundary a i Z).support : Set C) =
      i '' (a ⁻¹' (Z : Set X)) ∪ (Set.range i)ᶜ :=
  extendedClosed_coe a i Z

/-- Surjectivity of the actual alteration makes the constructed closed support proper. -/
theorem extendedClosed_ne_top (a : S ⟶ X) [IsAlteration a]
    (i : S ⟶ C) [IsOpenImmersion i] (Z : Closeds X) (hZ : Z ≠ ⊤) :
    extendedClosed a i Z ≠ ⊤ := by
  have hZset : (Z : Set X) ≠ Set.univ := fun h => hZ (SetLike.coe_injective h)
  have hnotall : ¬ ∀ x : X, x ∈ Z := fun h => hZset (Set.eq_univ_iff_forall.mpr h)
  obtain ⟨x, hx⟩ := not_forall.mp hnotall
  obtain ⟨s, hs⟩ := IsAlteration.surjective a x
  have hnot : i s ∉ extendedClosed a i Z := by
    change i s ∉ (i '' (a ⁻¹' (Z : Set X))ᶜ)ᶜ
    apply not_not.mpr
    refine ⟨s, ?_, rfl⟩
    change a s ∉ Z
    rwa [hs]
  intro h
  exact hnot (h.symm ▸ Set.mem_univ _)

end DeJongAlterations.Geometry.CurveBoundary
