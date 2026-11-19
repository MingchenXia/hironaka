import Hironaka.Geometry.ProjectiveSecantProjectionIsomorphismUnion

/-!
# Genuine native birationality of the SAME actual finite map from original local point data on every component
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace Hironaka.Geometry.ProjectiveSecant

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- An original open meeting EVERY original irreducible component is dense, with no irreducibility or Noetherian assumption on the whole space. -/
theorem original_open_dense_of_meets_components {T : Type u} [TopologicalSpace T]
    (U : Opens T) (h : ∀ C ∈ irreducibleComponents T, (C ∩ (U : Set T)).Nonempty) :
    Dense (U : Set T) := by
  intro x
  have hc : irreducibleComponent x ⊆ closure (irreducibleComponent x ∩ (U : Set T)) :=
    subset_closure_inter_of_isPreirreducible_of_isOpen isIrreducible_irreducibleComponent.2 U.isOpen
      (h _ (irreducibleComponent_mem_irreducibleComponents x))
  exact closure_mono Set.inter_subset_right (hc mem_irreducibleComponent)

/-- Original componentwise point local data internally give native BR of the SAME actual finite map onto its SAME actual native image, retaining the whole original schemes and all nilpotents. No dense-open, image or birational certificate is supplied. -/
theorem toImage_birationalOver_of_component_point_data
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f]
    (hpoints : ∀ C ∈ irreducibleComponents X, ∃ x ∈ C,
      (∀ z : X, f z = f x → z = x) ∧
      (f.stalkMap x).hom.FormallyUnramified ∧ IsIso (f.residueFieldMap x)) :
    Scheme.BirationalOver f.toImage (𝟙 f.image) := by
  let I := {C : Set X // C ∈ irreducibleComponents X}
  choose x hx hfibre hfu hres using (fun C : I => hpoints C.1 C.2)
  have hW (C : I) : ∃ W : f.image.Opens, f.toImage (x C) ∈ W ∧ IsIso (f.toImage ∣_ W) := by
    let := hres C
    exact exists_native_image_target_open_isIso_of_finite_point_data f (x C) (hfibre C) (hfu C)
  choose W hxW hIso using hW
  let U : f.image.Opens := ⨆ C : I, W C
  let : IsIso (f.toImage ∣_ U) := original_morphismRestrict_iSup_isIso f.toImage W hIso
  have hs : Dense (f.toImage ⁻¹ᵁ U : Set X) := by
    apply original_open_dense_of_meets_components
    intro C hC
    refine ⟨x ⟨C, hC⟩, hx ⟨C, hC⟩, ?_⟩
    exact (le_iSup W ⟨C, hC⟩) (hxW ⟨C, hC⟩)
  let : IsFinite f.toImage := toImage_isFinite f
  let : IsSchemeTheoreticallyDominant f.toImage := toImage_isSchemeTheoreticallyDominant f
  have ht : Dense (U : Set f.image) :=
    f.toImage.denseRange.dense_of_mapsTo f.toImage.continuous hs (fun _ h => h)
  let e : X.PartialIso f.image := {
    source := f.toImage ⁻¹ᵁ U
    dense_source := hs
    target := U
    dense_target := ht
    iso := asIso (f.toImage ∣_ U) }
  refine ⟨e, ?_⟩
  change (f.toImage ∣_ U) ≫ U.ι ≫ 𝟙 f.image = (f.toImage ⁻¹ᵁ U).ι ≫ f.toImage
  rw [Category.comp_id, morphismRestrict_ι]

end Hironaka.Geometry.ProjectiveSecant
