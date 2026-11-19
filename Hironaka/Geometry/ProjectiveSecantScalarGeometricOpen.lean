import Hironaka.Geometry.ProjectiveSecantGeometricOpen
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen

/-!
# The same original dense geometric open on the actual canonical scalar pullback
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace Hironaka.Geometry.ProjectiveSecant

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (k L : Type u) [Field k] [Field L] (φ : k →+* L)
  {X : Scheme.{u}} (p : X ⟶ Spec (.of k)) (U : X.Opens)

/-- The actual inverse image of the same specified original open under the actual canonical scalar projection. -/
def originalScalarOpen : (pullback p (Spec.map (CommRingCat.ofHom φ)) : Scheme.{u}).Opens :=
  pullback.fst p (Spec.map (CommRingCat.ofHom φ)) ⁻¹ᵁ U

/-- Actual field-scalar openness preserves original density on the same whole canonical source, with no source integrality or reducedness. -/
theorem originalScalarOpen_dense (hU : Dense (U : Set X)) :
    Dense (originalScalarOpen k L φ p U :
      Set (pullback p (Spec.map (CommRingCat.ofHom φ)) : Scheme.{u})) := by
  let π := pullback.fst p (Spec.map (CommRingCat.ofHom φ))
  let : UniversallyOpen π := inferInstance
  rw [dense_iff_inter_open]
  intro T hT hTn
  obtain ⟨y, hyimage, hyU⟩ := hU.inter_open_nonempty _ (π.isOpenMap T hT) (hTn.image π)
  obtain ⟨x, hxT, rfl⟩ := hyimage
  exact ⟨x, hxT, hyU⟩

/-- The actual original restriction square pasted with the native canonical scalar square retains both whole original coefficient triangles. -/
theorem originalScalarOpen_isPullback :
    IsPullback
      (pullback.fst p (Spec.map (CommRingCat.ofHom φ)) ∣_ U)
      ((originalScalarOpen k L φ p U).ι ≫ pullback.snd p (Spec.map (CommRingCat.ofHom φ)))
      (U.ι ≫ p) (Spec.map (CommRingCat.ofHom φ)) :=
  (isPullback_morphismRestrict (pullback.fst p (Spec.map (CommRingCat.ofHom φ))) U).paste_vert
    (IsPullback.of_hasPullback p (Spec.map (CommRingCat.ofHom φ)))

/-- The same original geometric open retains native geometric reducedness for its exact actual restricted scalar coefficient map. -/
theorem originalScalarOpen_geometricallyReduced [GeometricallyReduced (U.ι ≫ p)] :
    GeometricallyReduced
      ((originalScalarOpen k L φ p U).ι ≫ pullback.snd p (Spec.map (CommRingCat.ofHom φ))) :=
  MorphismProperty.of_isPullback (originalScalarOpen_isPullback k L φ p U) inferInstance

end Hironaka.Geometry.ProjectiveSecant
