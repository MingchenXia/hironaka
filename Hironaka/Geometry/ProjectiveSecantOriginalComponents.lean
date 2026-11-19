import Hironaka.Geometry.ProjectiveSecantGeometricOpen
import Hironaka.Geometry.ProjectiveModification
import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Actual integral component opens inside the original dense geometrically reduced open
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace Hironaka.Geometry.ProjectiveSecant

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Original projectivity and the actual closed immersion internally supply Noetherianity. -/
theorem originalProjectiveSource_isNoetherian
    (k : Type u) [Field k] (m : ℕ) {X : Scheme.{u}}
    (i : X ⟶ projectiveSpace k m) [IsClosedImmersion i] : IsNoetherian X := by
  let f := i ≫ projectiveSpaceStructure k m
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  exact {}

variable (k : Type u) [Field k] (m : ℕ) {X : Scheme.{u}}
  (i : X ⟶ projectiveSpace k m) [IsClosedImmersion i]
  (C : Set X) (hC : C ∈ irreducibleComponents X)

/-- An actual native original nonempty open contained in the specified original component. -/
def originalComponentOpen : X.Opens := by
  letI : IsNoetherian X := originalProjectiveSource_isNoetherian k m i
  let h := NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent C hC
  exact ⟨h.choose, h.choose_spec.1⟩

/-- The internally constructed original component open really is nonempty. -/
theorem originalComponentOpen_nonempty : (originalComponentOpen k m i C hC : Set X).Nonempty := by
  let : IsNoetherian X := originalProjectiveSource_isNoetherian k m i
  exact (NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent C hC).choose_spec.2.1

/-- Its actual points lie on the specified original component. -/
theorem originalComponentOpen_subset_component : (originalComponentOpen k m i C hC : Set X) ⊆ C := by
  let : IsNoetherian X := originalProjectiveSource_isNoetherian k m i
  exact (NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent C hC).choose_spec.2.2

variable (U : X.Opens)

/-- The actual component neighbourhood is intersected with the unchanged original dense geometric open. -/
def originalComponentGeometricOpen : X.Opens := U ⊓ originalComponentOpen k m i C hC

/-- Original density internally makes this actual component neighbourhood nonempty. -/
theorem originalComponentGeometricOpen_nonempty (hU : Dense (U : Set X)) :
    (originalComponentGeometricOpen k m i C hC U : Set X).Nonempty := by
  obtain ⟨x, hxV, hxU⟩ := hU.inter_open_nonempty _
    (originalComponentOpen k m i C hC).isOpen (originalComponentOpen_nonempty k m i C hC)
  exact ⟨x, hxU, hxV⟩

/-- The actual new open lies in the exact original geometric open. -/
theorem originalComponentGeometricOpen_le_original : originalComponentGeometricOpen k m i C hC U ≤ U :=
  inf_le_left

/-- It still lies on the exact original component, not a replacement component scheme. -/
theorem originalComponentGeometricOpen_subset_component :
    (originalComponentGeometricOpen k m i C hC U : Set X) ⊆ C := by
  intro x hx
  exact originalComponentOpen_subset_component k m i C hC hx.2

/-- All actual field base changes of this original source open remain reduced. -/
theorem originalComponentGeometricOpen_geometricallyReduced
    [GeometricallyReduced (U.ι ≫ (i ≫ projectiveSpaceStructure k m))] :
    GeometricallyReduced ((originalComponentGeometricOpen k m i C hC U).ι ≫
      (i ≫ projectiveSpaceStructure k m)) := by
  have h := geometricallyReduced_open_source
    (X.homOfLE (originalComponentGeometricOpen_le_original k m i C hC U))
    (U.ι ≫ (i ≫ projectiveSpaceStructure k m))
  simpa only [← Category.assoc, Scheme.homOfLE_ι] using h

/-- Actual original geometric reducedness and the internally constructed component open give a genuine integral source open. -/
theorem originalComponentGeometricOpen_isIntegral (hU : Dense (U : Set X))
    [GeometricallyReduced (U.ι ≫ (i ≫ projectiveSpaceStructure k m))] :
    IsIntegral (originalComponentGeometricOpen k m i C hC U) := by
  let W := originalComponentGeometricOpen k m i C hC U
  have hW : (W : Set X).Nonempty := originalComponentGeometricOpen_nonempty k m i C hC U hU
  let : IrreducibleSpace W := isIrreducible_iff_irreducibleSpace.mp
    (hC.1.2.subset_irreducible hW W.isOpen (le_refl _) (originalComponentGeometricOpen_subset_component k m i C hC U))
  let : GeometricallyReduced (W.ι ≫ (i ≫ projectiveSpaceStructure k m)) :=
    originalComponentGeometricOpen_geometricallyReduced k m i C hC U
  let : IsReduced W := isReduced_over_field_of_geometricallyReduced (W.ι ≫ (i ≫ projectiveSpaceStructure k m))
  exact isIntegral_of_irreducibleSpace_of_isReduced _

end Hironaka.Geometry.ProjectiveSecant
