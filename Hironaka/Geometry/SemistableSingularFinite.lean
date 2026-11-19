import Hironaka.Geometry.SemistableCurve
import Hironaka.Geometry.FiberDimensionUpperSemicontinuityClosedCover
import Hironaka.Geometry.RelativeUnramifiedClosedPoints
import Hironaka.Geometry.RelativeUnramifiedGeometricFibers
import Hironaka.Geometry.RelativeUnramifiedResidueComposition
import Hironaka.Geometry.NodeCompletedLocalGeometricAssociativity
import Hironaka.Algebra.NodeFittingGeometricIdealSheaf
import Hironaka.Algebra.NodeFittingGeometricUVStalk
import Hironaka.Algebra.NodeFittingGeometricPullback
import Hironaka.Algebra.NodeFittingOmegaFinitePresentation

/-! # The actual first-Fitting singular scheme is finite, unramified and finitely presented

This proves the conclusion of source 2.21 over an arbitrary base. Original
point-residue finite separability is derived, never an input.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace Hironaka.Geometry.SemistableCurve

open Hironaka.Algebra NodeFittingOmegaGluing
  NodeCompletedLocalGeometricChart NodeCompletedLocalGeometricAssociativity
  NodeCompletedLocalGeometricFiberUV
  NodeFittingGeometricPullback

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u
variable {X S : Scheme.{u}} (f : X ⟶ S) [IsSemistableCurve f]

/-- Pure one-dimensional components bound the actual whole geometric fibre dimension. -/
theorem geometricFiber_dimension_le_one (K : Type u) [Field K] [IsAlgClosed K]
    (a : Spec (.of K) ⟶ S) : topologicalKrullDim (pullback (C := Scheme.{u}) f a) ≤ 1 := by
  rw [FiberDimensionUpperSemicontinuityClosedCover.topologicalKrullDim_eq_iSup_componentDimension]
  apply iSup_le
  intro C
  exact (IsSemistableCurve.pureGeometricFibers K a C.val C.property).le

/-- The SAME actual pulled original singular morphism is unramified over the geometric field. -/
theorem pulledSingular_formallyUnramified (s : S) (K : Type u) [Field K]
    [IsAlgClosed K] [Algebra (S.residueField s) K] :
    FormallyUnramified
      (((idealSheaf f 1).comap (pullback.fst f (originalFieldMap s K))).subschemeι ≫
        pullback.snd f (originalFieldMap s K)) := by
  let a := originalFieldMap s K
  let q := pullback.snd f a
  let I := (idealSheaf f 1).comap (pullback.fst f a)
  let : LocallyOfFinitePresentation I.subschemeι := by
    dsimp only [I, a]
    rw [NodeFittingGeometricIdealSheaf.originalPullback_eq_geometricIdealSheaf]
    exact NodeFittingOmegaFinitePresentation.inclusion_locallyOfFinitePresentation q 1
  apply RelativeUnramified.formallyUnramified_overField_of_closed_stalk_equiv
    (I.subschemeι ≫ q)
  intro z hz
  have hy : IsClosed ({I.subschemeι z} : Set (pullback (C := Scheme.{u}) f a)) := by
    simpa only [Set.image_singleton] using I.subschemeι.isClosedEmbedding.isClosedMap _ hz
  rcases IsSemistableCurve.geometricNodes K a (I.subschemeι z) hy with hs | hn
  · exact False.elim
      (NodeFittingGeometricIdealSheaf.originalPullback_subscheme_image_not_mem_smoothLocus
        f s K (geometricFiber_dimension_le_one f K a) z hs)
  · obtain ⟨e⟩ := hn
    exact ⟨NodeFittingGeometricUVStalk.geometricNodeStalkEquiv f s K z e⟩

/-- The ORIGINAL first-Fitting family morphism is formally unramified over the arbitrary base. -/
theorem singular_formallyUnramified : FormallyUnramified (fittingMorphism f 1) := by
  let g := fittingMorphism f 1
  let : LocallyOfFinitePresentation g :=
    NodeFittingOmegaFinitePresentation.fittingMorphism_locallyOfFinitePresentation f 1
  apply RelativeUnramified.formallyUnramified_of_geometricFibers g
  intro s
  let K := AlgebraicClosure (S.residueField s)
  let a := originalFieldMap s K
  let e := geometricFittingPullbackIso f s K 1
  have hg : FormallyUnramified (pullback.snd g a) := by
    apply (MorphismProperty.cancel_left_of_respectsIso @FormallyUnramified e.hom _).mp
    rw [geometricFittingPullbackIso_hom_snd]
    exact pulledSingular_formallyUnramified f s K
  change FormallyUnramified (fieldProjection g s K)
  rw [← geometricFiberIso_field g s K]
  exact MorphismProperty.comp_mem @FormallyUnramified _ _ inferInstance hg

/-- The full original assertion 2.21: finite, unramified, and finite presentation. -/
theorem singular_finite_unramified_finitePresentation :
    IsFinite (fittingMorphism f 1) ∧ FormallyUnramified (fittingMorphism f 1) ∧
      LocallyOfFinitePresentation (fittingMorphism f 1) := by
  let : FormallyUnramified (fittingMorphism f 1) := singular_formallyUnramified f
  let : IsProper (fittingMorphism f 1) := by
    change IsProper ((idealSheaf f 1).subschemeι ≫ f)
    infer_instance
  exact ⟨RelativeUnramified.isFinite (fittingMorphism f 1), inferInstance,
    NodeFittingOmegaFinitePresentation.fittingMorphism_locallyOfFinitePresentation f 1⟩

/-- Finite separability at the ORIGINAL ambient singular point follows from 2.21. -/
theorem originalSingularResidue_finite_separable (z : (idealSheaf f 1).subscheme) :
    letI : Algebra (S.residueField (f ((idealSheaf f 1).subschemeι z)))
      (X.residueField ((idealSheaf f 1).subschemeι z)) :=
      (f.residueFieldMap ((idealSheaf f 1).subschemeι z)).hom.toAlgebra
    Module.Finite (S.residueField (f ((idealSheaf f 1).subschemeι z)))
      (X.residueField ((idealSheaf f 1).subschemeι z)) ∧
    Algebra.IsSeparable (S.residueField (f ((idealSheaf f 1).subschemeι z)))
      (X.residueField ((idealSheaf f 1).subschemeι z)) := by
  let : LocallyOfFinitePresentation (fittingMorphism f 1) :=
    NodeFittingOmegaFinitePresentation.fittingMorphism_locallyOfFinitePresentation f 1
  let : FormallyUnramified ((idealSheaf f 1).subschemeι ≫ f) :=
    singular_formallyUnramified f
  exact RelativeUnramified.pointResidue_finite_separable_of_comp
    (idealSheaf f 1).subschemeι f z

end Hironaka.Geometry.SemistableCurve
