import Hironaka.Geometry.NodeFamilyTower
import Hironaka.Geometry.NodeFamilyDimension
import Hironaka.Geometry.RationalCoordinateMapGenericFiberDimension

/-! Exact whole-space dimension of the actual fibres of the global finite node tower. -/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace Hironaka.Geometry.NodeFamilyTowerDimension

open Algebra.NodeBlowupChart NodeFamilyTower NodeFamilyFlat NodeFamilyDimension
open MonomialBlowupTower MonomialBlowupTowerCharts MonomialBlowupTowerRegular

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The actual pullback of a chart to a fibre is its actual composite fibre. -/
def chartFiberIso {X U S : Scheme.{u}} (f : U ⟶ X) (g : X ⟶ S) (s : S) :
    pullback (g.fiberι s) f ≅ (f ≫ g).fiber s :=
  ((IsPullback.of_hasPullback (g.fiberι s) f).flip.paste_vert
    (IsPullback.of_hasPullback g (S.fromSpecResidueField s))).isoPullback

variable {A : Type u} [CommRing A]

private theorem chart_fiber_dimension {l : List A} {n : ℕ} {P q : A}
    (C : ChartData l n P q) (p : PrimeSpectrum A) (i : Option C.I) :
    topologicalKrullDim ((C.openCover.pullback₁ ((familyMorphism l n).fiberι p)).X i) = 1 := by
  change topologicalKrullDim (pullback ((familyMorphism l n).fiberι p) (C.map i) : Scheme.{u}) = 1
  rw [IsHomeomorph.topologicalKrullDim_eq _
    (chartFiberIso (C.map i) (familyMorphism l n) p).hom.homeomorph.isHomeomorph]
  change FiberDimension.fiberDimension (C.map i ≫ familyMorphism l n) p = 1
  cases i with
  | none =>
    change FiberDimension.fiberDimension (C.continuationInclusion ≫ familyMorphism l n) p = 1
    rw [chart_coefficient_triangle C.continuationRingMap C.continuationInclusion C.continuation_structure]
    exact nodeFiber_dimension q p
  | some i =>
    change FiberDimension.fiberDimension (C.inclusion i ≫ familyMorphism l n) p = 1
    rw [chart_coefficient_triangle (C.ringMap i) (C.inclusion i) (C.inclusion_structure i)]
    exact nodeFiber_dimension (C.factor i) p

private theorem fiber_dimension_of_charts {l : List A} {n : ℕ} {P q : A}
    (C : ChartData l n P q) (p : PrimeSpectrum A) :
    FiberDimension.fiberDimension (familyMorphism l n) p = 1 := by
  let 𝒰 := C.openCover.pullback₁ ((familyMorphism l n).fiberι p)
  apply le_antisymm
  · apply FunctionFieldDimension.topologicalKrullDim_le_of_openCover _ 1 𝒰
    intro i
    change Option C.I at i
    exact (chart_fiber_dimension C p i).le
  · have hle := (𝒰.f (none : Option C.I)).isOpenEmbedding.isEmbedding.isInducing.topologicalKrullDim_le
    exact (chart_fiber_dimension C p none).symm.le.trans hle

variable [IsDomain A]

/-- Every actual fibre of every processed finite prefix has whole-space Krull dimension one. -/
theorem prefix_fiber_dimension (l : List A) (hl : (0 : A) ∉ l)
    (a b : List A) (hab : l = a ++ b) (p : PrimeSpectrum A) :
    FiberDimension.fiberDimension (familyMorphism l a.length) p = 1 := by
  obtain ⟨C⟩ := nonempty_charts l hl a b hab
  exact fiber_dimension_of_charts C p

/-- The actual final global family has whole-space fibre dimension one at every base point. -/
theorem final_fiber_dimension (l : List A) (hl : (0 : A) ∉ l) (p : PrimeSpectrum A) :
    FiberDimension.fiberDimension (resolutionMorphism l ≫ nodeMorphism l.prod) p = 1 :=
  prefix_fiber_dimension l hl l [] (by simp) p

end Hironaka.Geometry.NodeFamilyTowerDimension
