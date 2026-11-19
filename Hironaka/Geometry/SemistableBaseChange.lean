import Hironaka.Geometry.SemistableCurve
import Hironaka.Geometry.CurveFibrationBaseChangeFibers

/-! Semistability of the actual pullback, with its original geometric field actions. -/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace Hironaka.Geometry.SemistableBaseChange

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

/-- An actual over-field scheme isomorphism preserves the original completed-node condition. -/
theorem ordinaryDoublePoint_iff_of_iso {K : Type u} [Field K]
    {Y Z : Scheme.{u}} (e : Y ≅ Z) (qY : Y ⟶ Spec (.of K))
    (qZ : Z ⟶ Spec (.of K)) (he : e.hom ≫ qZ = qY) (y : Y) :
    IsGeometricOrdinaryDoublePoint qY y ↔ IsGeometricOrdinaryDoublePoint qZ (e.hom y) := by
  let := Scheme.completedLocalRingAlgebra qY y
  let := Scheme.completedLocalRingAlgebra qZ (e.hom y)
  let E := Scheme.completedLocalRingAlgEquivOfIsoOver e qY qZ he y
  change Nonempty (Y.completedLocalRing y ≃ₐ[K] Algebra.NodeGeometricCompletionFormalUV.FormalUV K) ↔
    Nonempty (Z.completedLocalRing (e.hom y) ≃ₐ[K]
      Algebra.NodeGeometricCompletionFormalUV.FormalUV K)
  exact ⟨fun ⟨eY⟩ => ⟨E.trans eY⟩, fun ⟨eZ⟩ => ⟨E.symm.trans eZ⟩⟩

/-- Every actual base change of the geometric completed-node semistable curve is semistable. -/
instance pullback_isSemistableCurve {X S S' : Scheme.{u}} (f : X ⟶ S)
    [IsSemistableCurve f] (g : S' ⟶ S) : IsSemistableCurve (pullback.snd f g) where
  toFlat := inferInstance
  toIsProper := inferInstance
  toLocallyOfFinitePresentation := inferInstance
  toGeometricallyConnected := inferInstance
  toGeometricallyReduced := inferInstance
  pureGeometricFibers := by
    intro K _ _ a C hC
    exact CurveFibrationBaseChange.component_dimension_of_homeomorph
      (pullbackLeftPullbackSndIso f g a).hom.homeomorph 1
      (IsSemistableCurve.pureGeometricFibers K (a ≫ g)) C hC
  geometricNodes := by
    intro K _ _ a y hy
    let e : pullback (pullback.snd f g) a ≅ pullback f (a ≫ g) :=
      pullbackLeftPullbackSndIso f g a
    have he : e.hom ≫ pullback.snd f (a ≫ g) = pullback.snd (pullback.snd f g) a :=
      pullbackLeftPullbackSndIso_hom_snd f g a
    have hclosed : IsClosed ({e.hom y} : Set (pullback f (a ≫ g) : Scheme.{u})) := by
      simpa only [Set.image_singleton, Scheme.Hom.homeomorph_apply] using
        e.hom.homeomorph.isClosedMap {y} hy
    rcases IsSemistableCurve.geometricNodes K (a ≫ g) (e.hom y) hclosed with hs | hn
    · left
      have hs' : y ∈ e.hom ⁻¹ᵁ (pullback.snd f (a ≫ g)).smoothLocus := hs
      rw [Scheme.Hom.preimage_smoothLocus_eq] at hs'
      simpa only [he] using hs'
    · exact Or.inr ((ordinaryDoublePoint_iff_of_iso e _ _ he y).mpr hn)

end Hironaka.Geometry.SemistableBaseChange
