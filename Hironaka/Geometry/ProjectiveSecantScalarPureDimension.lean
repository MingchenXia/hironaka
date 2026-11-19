import Hironaka.Geometry.ProjectiveSecantFlatComponents
import Hironaka.Geometry.ProjectiveSecantIntegralDominantDimension
import Hironaka.Geometry.FiniteBirationalNormalReducedComponents
import Hironaka.Geometry.ProjectiveCompactification

/-!
# Actual algebraic scalar components keep the original pure dimensions
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace Hironaka.Geometry.ProjectiveSecant

open FiniteBirationalNormal

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The actual intrinsic component scheme and its entire actual native integral image internally preserve the original component dimension. -/
theorem component_image_dimension_eq_of_integral
    {k : Type u} [Field k] {X Y : Scheme.{u}}
    (p : Y ⟶ Spec (.of k)) [LocallyOfFiniteType p]
    (f : X ⟶ Y) [IsIntegralHom f] (D : irreducibleComponents X) :
    topologicalKrullDim D.val = topologicalKrullDim (f '' D.val) := by
  let g := reducedComponentInclusion X D ≫ f
  let : IsIntegral g.image := ProjectiveCompactification.image_isIntegral g
  have : IsIntegralHom (g.toImage ≫ g.imageι) := by
    rw [g.toImage_imageι]
    infer_instance
  let : IsIntegralHom g.toImage := IsIntegralHom.of_comp g.toImage g.imageι
  have hdim := topologicalKrullDim_eq_of_integral_dominant (g.imageι ≫ p) g.toImage
  have hRg : Set.range g = f '' D.val := by
    change Set.range (f ∘ reducedComponentInclusion X D) = _
    rw [Set.range_comp, reducedComponentInclusion_range]
  have hs : (g.ker.support : Set Y) = f '' D.val := by
    rw [g.support_ker, hRg, (f.isClosedMap D.val
      (isClosed_of_mem_irreducibleComponents D.val D.property)).closure_eq]
  have hi : topologicalKrullDim g.image = topologicalKrullDim (f '' D.val) :=
    IsHomeomorph.topologicalKrullDim_eq _ (Homeomorph.setCongr hs).isHomeomorph
  exact hdim.trans hi

/-- Actual flatness internally identifies actual component images, and actual integral dimensions preserve every original pure component dimension. -/
theorem component_dimension_of_flat_integral
    {k : Type u} [Field k] {X Y : Scheme.{u}}
    (p : Y ⟶ Spec (.of k)) [LocallyOfFiniteType p]
    (f : X ⟶ Y) [Flat f] [IsIntegralHom f] (d : ℕ)
    (hpure : ∀ C ∈ irreducibleComponents Y, topologicalKrullDim C = d)
    (D : Set X) (hD : D ∈ irreducibleComponents X) : topologicalKrullDim D = d :=
  (component_image_dimension_eq_of_integral p f ⟨D, hD⟩).trans
    (hpure (f '' D) (image_component_mem_irreducibleComponents_of_flat_integral f D hD))

/-- The exact actual canonical algebraic scalar pullback retains the ORIGINAL pure dimensions on EVERY actual native component, without any scalar-purity certificate. -/
theorem algebraicScalar_component_dimension
    (k L : Type u) [Field k] [Field L] [Algebra k L] [Algebra.IsAlgebraic k L]
    {X : Scheme.{u}} (p : X ⟶ Spec (.of k)) [LocallyOfFiniteType p] (d : ℕ)
    (hpure : ∀ C ∈ irreducibleComponents X, topologicalKrullDim C = d)
    (D : Set (pullback p (Spec.map (CommRingCat.ofHom (algebraMap k L))) : Scheme.{u}))
    (hD : D ∈ irreducibleComponents (pullback p (Spec.map (CommRingCat.ofHom (algebraMap k L))) : Scheme.{u})) :
    topologicalKrullDim D = d := by
  let π := pullback.fst p (Spec.map (CommRingCat.ofHom (algebraMap k L)))
  let : IsIntegralHom π := algebraicScalarProjection_isIntegralHom k L p
  exact component_dimension_of_flat_integral p π d hpure D hD

end Hironaka.Geometry.ProjectiveSecant
