import Hironaka.Geometry.ProjectiveSecantGeometricGenericAffine

/-!
# The actual generic point of an original geometrically reduced integral source is smooth
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace Hironaka.Geometry.ProjectiveSecant

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Original integral source geometry internally supplies the actual affine domain, exact coefficient algebra and separating basis needed for the same original generic point to be smooth. -/
theorem genericPoint_mem_smoothLocus_of_geometricallyReduced
    {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X]
    (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p] [GeometricallyReduced p] :
    genericPoint X ∈ p.smoothLocus := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, _⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    (show genericPoint X ∈ (⊤ : X.Opens) from trivial) (⊤ : X.Opens).isOpen
  let A := Γ(X, U)
  let a := hU.fromSpec
  let : Nonempty (Spec (CommRingCat.of A)) := ⟨hU.primeIdealOf ⟨genericPoint X, hxU⟩⟩
  let : IsIntegral (Spec (CommRingCat.of A)) := isIntegral_of_isOpenImmersion a
  let : IsDomain A := (affine_isIntegral_iff (CommRingCat.of A)).mp inferInstance
  let β : CommRingCat.of k ⟶ CommRingCat.of A := Spec.preimage (a ≫ p)
  let : Algebra k A := β.hom.toAlgebra
  have hβ : Spec.map (CommRingCat.ofHom (algebraMap k A)) = a ≫ p := Spec.map_preimage _
  let : GeometricallyReduced (Spec.map (CommRingCat.ofHom (algebraMap k A))) := by
    rw [hβ]
    exact geometricallyReduced_open_source a p
  let : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap k A))) := by
    rw [hβ]
    infer_instance
  have hft : (algebraMap k A).FiniteType :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp inferInstance
  let : Algebra.FiniteType k A := hft
  have hpoint := affine_genericPoint_mem_smoothLocus_of_geometricallyReduced k A
  have hpoint' : genericPoint (Spec (CommRingCat.of A)) ∈ (a ≫ p).smoothLocus := by
    rw [Scheme.Hom.mem_smoothLocus] at hpoint ⊢
    exact Eq.mp (congrArg (fun g : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of k) =>
      (g.stalkMap (genericPoint (Spec (CommRingCat.of A)))).hom.FormallySmooth) hβ) hpoint
  rw [← Scheme.Hom.preimage_smoothLocus_eq, Scheme.Hom.mem_preimage] at hpoint'
  have hη : a (genericPoint (Spec (CommRingCat.of A))) = genericPoint X :=
    genericPoint_eq_of_isOpenImmersion a
  exact hη ▸ hpoint'

/-- Actual original geometric reducedness internally proves density of the exact original smooth locus over arbitrary fields. -/
theorem dense_smoothLocus_of_geometricallyReduced
    {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X]
    (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p] [GeometricallyReduced p] :
    Dense (p.smoothLocus : Set X) :=
  p.smoothLocus.isOpen.dense ⟨genericPoint X, genericPoint_mem_smoothLocus_of_geometricallyReduced p⟩

end Hironaka.Geometry.ProjectiveSecant
