import Hironaka.Geometry.AlterationBasic
import Mathlib.AlgebraicGeometry.Geometrically.Reduced
import Mathlib.RingTheory.Unramified.Field

/-!
# Actual reducedness and component etale opens

Unramified affine algebras over fields are reduced. Actual affine covers
and native base change therefore prove geometric reducedness of etale
morphisms. Native flat geometric reducedness then gives actual reduced
sources over reduced locally Noetherian schemes.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

noncomputable section

namespace Hironaka.Geometry.AlterationDominatingBaseChange

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {Z W : Scheme.{u}}

/-- Actual affine coordinate rings of an etale source over a field are
reduced, hence its actual scheme is reduced. -/
theorem isReduced_of_etale_field {K : Type u} [Field K]
    (p : Z ⟶ Spec (CommRingCat.of K)) [Etale p] : IsReduced Z := by
  let : ∀ i, IsReduced (Z.affineCover.X i) := by
    intro i
    let U := Z.affineCover.X i
    let a := U.isoSpec.inv ≫ Z.affineCover.f i ≫ p
    obtain ⟨φ, hφ⟩ := Spec.map_surjective a
    let : Etale (Spec.map φ) := by rw [hφ]; infer_instance
    let : Algebra K Γ(U, ⊤) := φ.hom.toAlgebra
    let : Algebra.Etale K Γ(U, ⊤) := RingHom.etale_algebraMap.mp
      ((HasRingHomProperty.Spec_iff (P := @Etale)).mp inferInstance)
    let : _root_.IsReduced Γ(U, ⊤) :=
      Algebra.FormallyUnramified.isReduced_of_field K Γ(U, ⊤)
    let : IsReduced (Spec Γ(U, ⊤)) := inferInstance
    exact isReduced_of_isOpenImmersion U.isoSpec.hom
  exact IsReduced.of_openCover Z Z.affineCover

/-- Etale morphisms are genuinely geometrically reduced, using actual
arbitrary field base changes and the actual affine ring theorem. -/
theorem etale_geometricallyReduced (p : Z ⟶ W) [Etale p] : GeometricallyReduced p where
  geometrically_isReduced := by
    intro K _ y T a b h
    let : Etale b := MorphismProperty.of_isPullback h inferInstance
    exact isReduced_of_etale_field b

/-- An actual etale morphism over a reduced locally Noetherian target has
an actual reduced source; neither reducedness nor fibre data is assumed. -/
theorem isReduced_of_etale (p : Z ⟶ W) [Etale p]
    [IsReduced W] [IsLocallyNoetherian W] : IsReduced Z := by
  let : GeometricallyReduced p := etale_geometricallyReduced p
  exact GeometricallyReduced.isReduced_of_flat_of_isLocallyNoetherian p

end Hironaka.Geometry.AlterationDominatingBaseChange
