import Hironaka.Geometry.ProjectiveSecantProjectionComponentFlatOpen
import Hironaka.Geometry.GenericFlatness

/-!
# Native generic etaleness of the unchanged finite map from actual original component geometry
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace Hironaka.Geometry.ProjectiveSecant

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Actual original component dimensions and original point stalks internally produce native generic etaleness of the unchanged original finite morphism; no flat, dominant, dense-open or generic-etale certificate is assumed. -/
theorem genericallyEtale_of_component_dimension_and_stalks
    {k : Type u} [Field k] {X Y : Scheme.{u}}
    (p : Y ⟶ Spec (CommRingCat.of k)) [IsVariety p] (f : X ⟶ Y) [IsFinite f]
    [LocallyOfFinitePresentation f]
    (hdim : ∀ C ∈ irreducibleComponents X, topologicalKrullDim Y ≤ topologicalKrullDim C)
    (hpoints : ∀ C ∈ irreducibleComponents X, ∃ x ∈ C, (f.stalkMap x).hom.FormallyUnramified) :
    IsGenericallyEtale f := by
  obtain ⟨A, hAd, hAfu⟩ := exists_dense_formallyUnramified_open_of_component_stalks f hpoints
  let : FormallyUnramified (A.ι ≫ f) := hAfu
  obtain ⟨V, hV, hflat⟩ := GenericFlatness.exists_nonempty_flat_of_isIntegral f
  let : Flat (f ∣_ V) := hflat
  have hPd := dense_preimage_open_of_component_dimensions p f hdim V (by simpa using hV)
  let W := A ⊓ f ⁻¹ᵁ V
  have hWd : Dense (W : Set X) := by
    rw [dense_iff_inter_open]
    intro T hT hTn
    have hTA : (T ∩ (A : Set X)).Nonempty := by
      obtain ⟨x, hxT, hxA⟩ := hAd.inter_open_nonempty T hT hTn
      exact ⟨x, hxT, hxA⟩
    obtain ⟨x, hxTA, hxP⟩ := hPd.inter_open_nonempty _ (hT.inter A.isOpen) hTA
    exact ⟨x, hxTA.1, hxTA.2, hxP⟩
  have htflat : W.ι ≫ f = X.homOfLE (show W ≤ f ⁻¹ᵁ V from inf_le_right) ≫
      (f ∣_ V) ≫ V.ι := by
    rw [morphismRestrict_ι, ← Category.assoc, Scheme.homOfLE_ι]
  let : Flat (W.ι ≫ f) := by rw [htflat]; infer_instance
  have htfu : W.ι ≫ f = X.homOfLE (show W ≤ A from inf_le_left) ≫ (A.ι ≫ f) := by
    rw [← Category.assoc, Scheme.homOfLE_ι]
  let : FormallyUnramified (W.ι ≫ f) := by
    rw [htfu]
    exact MorphismProperty.comp_mem @FormallyUnramified _ _ inferInstance inferInstance
  exact ⟨W, hWd, Etale.of_formallyUnramified_of_flat (W.ι ≫ f)⟩

end Hironaka.Geometry.ProjectiveSecant
