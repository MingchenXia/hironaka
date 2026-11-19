import Hironaka.Geometry.GenericFiberFunctionField
import Hironaka.Geometry.ProjectiveCurveFibrationFiberMaps
import Hironaka.Geometry.CurveBoundaryBasic
import Hironaka.Geometry.FiberDimensionOne

/-! # Actual closed bad loci in a proper generic curve fibration -/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace Hironaka.Geometry.CurveFibrationBadLocus

open FiberDimension ProjectiveCurveFibration

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {X S Z : Scheme.{u}} [IsIntegral X] [IsIntegral S]
  (f : X ⟶ S) [IsDominant f]

/-- An actual closed subscheme missing the generic point has zero-dimensional generic fibre. -/
theorem genericFiber_dimension_le_zero_of_closedImmersion
    (hgen : fiberDimension f (genericPoint S) ≤ 1)
    (i : Z ⟶ X) [IsClosedImmersion i]
    (hi : genericPoint X ∉ Set.range i) :
    fiberDimension (i ≫ f) (genericPoint S) ≤ 0 := by
  let := GenericFiberIntegral.genericFiber_isIntegral f
  let := GenericFiberFunctionField.genericFiberι_isDominant f
  let m := sourceFiberMap i f (genericPoint S)
  let : IsClosedImmersion m := by
    apply MorphismProperty.of_isPullback (sourceFiberMap_isPullback i f (genericPoint S)).flip
    infer_instance
  have hne (z : (i ≫ f).fiber (genericPoint S)) :
      m z ≠ genericPoint (f.fiber (genericPoint S)) := by
    intro hz
    have ht := congrArg (fun g : (i ≫ f).fiber (genericPoint S) ⟶ X => g z)
      (sourceFiberMap_fiberι i f (genericPoint S))
    have hη := genericPoint_map_of_isDominant (f.fiberι (genericPoint S))
    exact hi ⟨(i ≫ f).fiberι (genericPoint S) z,
      ht.symm.trans ((congrArg (f.fiberι (genericPoint S)) hz).trans hη)⟩
  let : T1Space ((i ≫ f).fiber (genericPoint S)) := by
    constructor
    intro z
    have hc := CurveBoundary.isClosed_singleton_of_ne_genericPoint hgen (m z) (hne z)
    convert hc.preimage m.continuous using 1
    ext w
    exact Set.mem_singleton_iff.trans (m.isEmbedding.injective.eq_iff).symm
  exact CurveBoundary.topologicalKrullDim_le_zero_of_t1 _

/-- Properness constructs an actual dense base open with no positive-dimensional bad fibre. -/
theorem exists_nonempty_dense_fiberDimension_le_zero [IsProper f]
    (hgen : fiberDimension f (genericPoint S) ≤ 1)
    (i : Z ⟶ X) [IsClosedImmersion i]
    (hi : genericPoint X ∉ Set.range i) :
    ∃ V : S.Opens, Nonempty V ∧ Dense (V : Set S) ∧
      ∀ s : V, fiberDimension (i ≫ f) s.val ≤ 0 := by
  have hc := FiberDimensionOne.isClosed_fiberDimensionGE_one (i ≫ f)
  let V : S.Opens := ⟨(fiberDimensionGE (i ≫ f) 1)ᶜ, hc.isOpen_compl⟩
  have hη : genericPoint S ∈ V := by
    intro h
    have hzero := genericFiber_dimension_le_zero_of_closedImmersion f hgen i hi
    exact (show (0 : WithBot ℕ∞) < 1 from zero_lt_one).not_ge (h.trans hzero)
  refine ⟨V, ⟨⟨genericPoint S, hη⟩⟩, V.isOpen.dense ⟨genericPoint S, hη⟩, ?_⟩
  intro s
  apply le_of_not_gt
  intro hpos
  apply s.property
  change (1 : WithBot ℕ∞) ≤ fiberDimension (i ≫ f) s.val
  simpa only [Nat.cast_zero, zero_add] using
    (ENat.WithBot.add_one_le_iff (n := 0) (m := fiberDimension (i ≫ f) s.val)).mpr hpos

end Hironaka.Geometry.CurveFibrationBadLocus
