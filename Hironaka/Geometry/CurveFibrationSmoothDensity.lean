import Hironaka.Geometry.CurveFibrationSmoothDensityTopology
import Hironaka.Geometry.CurveFibrationBadLocus
import Hironaka.Geometry.RelativeGenericSmoothness
import Hironaka.Geometry.FiberDimensionCurveComponents
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme

/-!
# Fibrewise density of the original smooth locus over a dense base open

For an integral proper generic curve with separably generated canonical
function-field extension, remove the actual positive-dimensional bad-fibre
locus. All remaining actual fibres have dense preimage of the ORIGINAL
relative smooth locus. Geometric-fibre density and markings are separate.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace Hironaka.Geometry.CurveFibrationSmoothDensity

open FiberDimension ProjectiveCurveFibration

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The actual induced fibre map has the actual inverse-image point range. -/
theorem range_sourceFiberMap {Z X S : Scheme.{u}} (i : Z ⟶ X) (f : X ⟶ S) (s : S) :
    Set.range (sourceFiberMap i f s) = (f.fiberι s) ⁻¹' Set.range i := by
  let hp := sourceFiberMap_isPullback i f s
  rw [← hp.isoPullback_hom_fst, Scheme.Hom.comp_base, TopCat.coe_comp,
    Set.range_comp, Set.range_eq_univ.mpr hp.isoPullback.hom.surjective, Set.image_univ]
  exact Scheme.Pullback.range_fst _ _

/-- In positive generic relative dimension no actual fibre has an open singleton. -/
theorem not_isOpen_singleton_fiber {X S : Scheme.{u}} [IsIntegral X] [IsIntegral S]
    (f : X ⟶ S) [IsDominant f] [LocallyOfFiniteType f]
    (hgen : (1 : WithBot ℕ∞) ≤ fiberDimension f (genericPoint S))
    (s : S) (z : f.fiber s) : ¬ IsOpen ({z} : Set (f.fiber s)) := by
  intro hz
  exact FiberDimensionCurveComponents.not_quasiFiniteAt_of_one_le_genericFiberDimension
    f hgen _ (FiberDimensionCurveComponents.quasiFiniteAt_of_isOpen_singleton_fiber f s z hz)

/-- Every actual residue fibre over a constructed dense base open meets the original smooth locus densely. -/
theorem exists_nonempty_dense_original_smoothLocus_fiberwise_dense
    {X S : Scheme.{u}} [IsIntegral X] [IsIntegral S]
    (f : X ⟶ S) [IsDominant f] [IsProper f] [LocallyOfFinitePresentation f]
    (hgen : fiberDimension f (genericPoint S) = 1)
    (hsep : RelativeGenericSmoothness.FunctionFieldSeparablyGenerated f) :
    ∃ V : S.Opens, Nonempty V ∧ Dense (V : Set S) ∧
      ∀ s : V, Dense ((f.fiberι s.val) ⁻¹' (f.smoothLocus : Set X)) := by
  let B : Closeds X := ⟨(f.smoothLocus : Set X)ᶜ, f.smoothLocus.isOpen.isClosed_compl⟩
  let D := Scheme.IdealSheafData.vanishingIdeal B
  have hη : genericPoint X ∉ Set.range D.subschemeι := by
    rw [D.range_subschemeι]
    exact not_not.mpr (RelativeGenericSmoothness.genericPoint_mem_smoothLocus f hsep)
  obtain ⟨V, hV, hVdense, hdim⟩ :=
    CurveFibrationBadLocus.exists_nonempty_dense_fiberDimension_le_zero f hgen.le D.subschemeι hη
  refine ⟨V, hV, hVdense, ?_⟩
  intro s
  let m := sourceFiberMap D.subschemeι f s.val
  let : IsClosedImmersion m := by
    apply MorphismProperty.of_isPullback (sourceFiberMap_isPullback D.subschemeι f s.val).flip
    infer_instance
  let : DiscreteTopology ((D.subschemeι ≫ f).fiber s.val) :=
    (FiberDimensionOne.fiberDimension_le_zero_iff_discreteTopology (D.subschemeι ≫ f) s.val).mp
      (hdim s)
  have hm : _root_.IsDiscrete (Set.range m) := m.isEmbedding.isInducing.isDiscrete_range
  have hrange : Set.range m = ((f.fiberι s.val) ⁻¹' (f.smoothLocus : Set X))ᶜ := by
    rw [range_sourceFiberMap, D.range_subschemeι]
    rfl
  have hdense := dense_compl_of_isDiscrete_of_no_open_singleton hm
    (not_isOpen_singleton_fiber f hgen.ge s.val)
  simpa only [hrange, compl_compl] using hdense

end Hironaka.Geometry.CurveFibrationSmoothDensity
