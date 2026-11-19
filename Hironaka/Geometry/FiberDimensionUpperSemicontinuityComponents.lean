import Hironaka.Geometry.FiberDimensionUpperSemicontinuityClosedCover
import Hironaka.Geometry.ReducedClosedSubscheme

/-!
# The actual reduced component family and its literal closed fiber cover

The native vanishing ideal constructs each component with its reduced
scheme structure. All component inclusions and actual fiber projections
are internal, and their finite closed-cover dimensions compute the original
scheme-theoretic fiber dimension.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace Hironaka.Geometry.FiberDimensionUpperSemicontinuityComponents

open FiberDimension FiberDimensionGenericFinite FiberDimensionUpperSemicontinuityClosedCover

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (X : Scheme.{u})

/-- The actual radical ideal cutting out the original irreducible component. -/
def componentIdeal (Z : irreducibleComponents X) : X.IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal ⟨Z.val, isClosed_of_mem_irreducibleComponents _ Z.property⟩

/-- The actual native reduced closed component subscheme. -/
abbrev componentScheme (Z : irreducibleComponents X) : Scheme.{u} :=
  (componentIdeal X Z).subscheme

/-- The literal original component inclusion. -/
def componentInclusion (Z : irreducibleComponents X) : componentScheme X Z ⟶ X :=
  (componentIdeal X Z).subschemeι

instance componentInclusion_isClosedImmersion (Z : irreducibleComponents X) :
    IsClosedImmersion (componentInclusion X Z) := by unfold componentInclusion; infer_instance

/-- The actual reduced component is integral, without a caller scheme certificate. -/
instance componentScheme_isIntegral (Z : irreducibleComponents X) : IsIntegral (componentScheme X Z) := by
  let : IsReduced (componentScheme X Z) :=
    ReducedClosedSubscheme.isReduced_vanishingIdeal_subscheme _
  let : IrreducibleSpace (componentScheme X Z) := by
    change IrreducibleSpace Z.val
    exact Subtype.irreducibleSpace Z.property.1
  exact isIntegral_of_irreducibleSpace_of_isReduced _

/-- The internally constructed component inclusions cover every original source point. -/
theorem componentInclusion_covers (x : X) :
    ∃ Z : irreducibleComponents X, ∃ z : componentScheme X Z, componentInclusion X Z z = x := by
  let Z : irreducibleComponents X :=
    ⟨irreducibleComponent x, irreducibleComponent_mem_irreducibleComponents x⟩
  exact ⟨Z, ⟨x, mem_irreducibleComponent⟩, rfl⟩

variable {X} {S : Scheme.{u}} (f : X ⟶ S) (s : S)

/-- The actual native fiber projection of the internally constructed closed component. -/
def componentFiberMap (Z : irreducibleComponents X) :
    (componentInclusion X Z ≫ f).fiber s ⟶ f.fiber s :=
  fiberProjection (componentInclusion X Z) f s

instance componentFiberMap_isClosedImmersion (Z : irreducibleComponents X) :
    IsClosedImmersion (componentFiberMap f s Z) := by
  unfold componentFiberMap fiberProjection
  infer_instance

/-- The literal original scheme fiber is covered by the actual component fibers. -/
theorem componentFiberMap_covers (z : f.fiber s) :
    ∃ Z : irreducibleComponents X, ∃ w, componentFiberMap f s Z w = z := by
  obtain ⟨Z, x, hx⟩ := componentInclusion_covers X (f.fiberι s z)
  obtain ⟨w, hw, -⟩ := Scheme.exists_preimage_of_isPullback
    (fiberProjection_isPullback (componentInclusion X Z) f s) z x hx.symm
  exact ⟨Z, w, hw⟩

/-- Noetherian source components internally compute every original fiber dimension. -/
theorem fiberDimension_eq_iSup_componentFiberDimension [NoetherianSpace X] :
    fiberDimension f s = ⨆ Z : irreducibleComponents X,
      fiberDimension (componentInclusion X Z ≫ f) s := by
  classical
  let : Fintype (irreducibleComponents X) :=
    NoetherianSpace.finite_irreducibleComponents.fintype
  let C : Finset (Set (f.fiber s)) := Finset.univ.image fun Z ↦ Set.range (componentFiberMap f s Z)
  have hdim (Z : irreducibleComponents X) :
      topologicalKrullDim (Set.range (componentFiberMap f s Z)) =
        fiberDimension (componentInclusion X Z ≫ f) s :=
    (IsHomeomorph.topologicalKrullDim_eq _ (componentFiberMap f s Z).isEmbedding.toHomeomorph.isHomeomorph).symm
  apply le_antisymm
  · apply topologicalKrullDim_le_of_finite_closed_cover C
    · intro D hD
      obtain ⟨Z, -, rfl⟩ := Finset.mem_image.mp hD
      exact (componentFiberMap f s Z).isClosedEmbedding.isClosed_range
    · intro z _
      obtain ⟨Z, w, hw⟩ := componentFiberMap_covers f s z
      exact ⟨Set.range (componentFiberMap f s Z), Finset.mem_image.mpr ⟨Z, Finset.mem_univ _, rfl⟩,
        w, hw⟩
    · intro D hD
      obtain ⟨Z, -, rfl⟩ := Finset.mem_image.mp hD
      rw [hdim]
      exact le_iSup (fun Z : irreducibleComponents X ↦ fiberDimension (componentInclusion X Z ≫ f) s) Z
  · apply iSup_le
    intro Z
    exact (componentFiberMap f s Z).isEmbedding.isInducing.topologicalKrullDim_le

end Hironaka.Geometry.FiberDimensionUpperSemicontinuityComponents
