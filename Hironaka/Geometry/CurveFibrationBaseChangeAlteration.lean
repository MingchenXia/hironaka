import Hironaka.Geometry.CurveFibrationBaseChange
import Hironaka.Geometry.AlterationDominatingBaseChangeGenericallyEtale

/-!
# The original whole-reduction projection is an actual alteration

The source is the actual reduction of the whole native pullback. Its
range is internally proved to be the unique native irreducible component.
The existing genuine component producers then apply to this original map.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open Hironaka.Geometry.RelativeChow

namespace Hironaka.Geometry.CurveFibrationBaseChange

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {X S Y T : Scheme.{u}}

private theorem dominant_of_generic_mem_range (a : T ⟶ X) [IsIntegral X]
    (h : genericPoint X ∈ Set.range a) : IsDominant a := by
  refine ⟨?_⟩
  rw [denseRange_iff_closure_range]
  apply Set.Subset.antisymm (Set.subset_univ _)
  rw [← (genericPoint_spec X).def]
  exact closure_mono (Set.singleton_subset_iff.mpr h)

/-- Both actual original projections dominate; the point above both generic points is produced. -/
theorem reduction_projections_isDominant [IsIntegral X] [IsIntegral Y] [IsIntegral S]
    (f : X ⟶ S) (g : Y ⟶ S) [IsDominant f] [IsDominant g] :
    IsDominant (reductionι f g ≫ pullback.fst f g) ∧
      IsDominant (reductionι f g ≫ pullback.snd f g) := by
  obtain ⟨z, hz₁, hz₂⟩ := Scheme.Pullback.exists_preimage_pullback
    (f := f) (g := g) (genericPoint X) (genericPoint Y)
    ((genericPoint_map_of_isDominant f).trans (genericPoint_map_of_isDominant g).symm)
  let w : reducedPullback f g := ⟨z, by trivial⟩
  exact ⟨dominant_of_generic_mem_range _ ⟨w, hz₁⟩,
    dominant_of_generic_mem_range _ ⟨w, hz₂⟩⟩

/-- The actual whole-reduction range is internally identified with the unique native component. -/
theorem reductionι_range_mem_irreducibleComponents [IsIntegral S] [IsIntegral Y]
    (f : X ⟶ S) [LocallyOfFinitePresentation f]
    (hη : GeometricallyIntegral (f.fiberToSpecResidueField (genericPoint S)))
    (hsm : ∀ (K : Type u) [Field K] (e : Spec (.of K) ⟶ S),
      Dense ((pullback.fst f e) ⁻¹' (f.smoothLocus : Set X)))
    (g : Y ⟶ S) [IsDominant g] :
    Set.range (reductionι f g) ∈ irreducibleComponents (pullback f g : Scheme.{u}) := by
  let : IrreducibleSpace (pullback f g : Scheme.{u}) := pullback_irreducibleSpace f hη hsm g
  rw [irreducibleComponents_eq_singleton]
  simp [reductionι, Scheme.IdealSheafData.range_subschemeι]

/-- The original projection from the actual whole reduction is an actual alteration. -/
theorem reduction_first_isAlteration [IsIntegral X] [IsIntegral S] (f : X ⟶ S)
    [LocallyOfFinitePresentation f] [IsDominant f]
    (g : Y ⟶ S) [hg : IsAlteration g]
    (hη : GeometricallyIntegral (f.fiberToSpecResidueField (genericPoint S)))
    (hsm : ∀ (K : Type u) [Field K] (e : Spec (.of K) ⟶ S),
      Dense ((pullback.fst f e) ⁻¹' (f.smoothLocus : Set X))) :
    IsAlteration (reductionι f g ≫ pullback.fst f g) := by
  let := hg.sourceIntegral
  let := reducedPullback_isIntegral f hη hsm g
  let := (reduction_projections_isDominant f g).1
  let := (reduction_projections_isDominant f g).2
  exact AlterationDominatingBaseChange.first_isAlteration f g (reductionι f g)

/-- The same original projection is generically etale when the actual base alteration is. -/
theorem reduction_first_isGenericallyEtale [IsIntegral X] [IsIntegral S]
    [AlgebraicGeometry.IsNoetherian X]
    (f : X ⟶ S) [LocallyOfFinitePresentation f] [IsDominant f]
    (g : Y ⟶ S) [hg : IsAlteration g]
    (hη : GeometricallyIntegral (f.fiberToSpecResidueField (genericPoint S)))
    (hsm : ∀ (K : Type u) [Field K] (e : Spec (.of K) ⟶ S),
      Dense ((pullback.fst f e) ⁻¹' (f.smoothLocus : Set X)))
    (hgEt : IsGenericallyEtale g) :
    IsGenericallyEtale (reductionι f g ≫ pullback.fst f g) := by
  let := hg.sourceIntegral
  let := reducedPullback_isIntegral f hη hsm g
  let := (reduction_projections_isDominant f g).2
  exact AlterationDominatingBaseChange.first_isGenericallyEtale f g hgEt (reductionι f g)
    (reductionι_range_mem_irreducibleComponents f hη hsm g)

/-- An actual relative closed embedding for the original whole-reduction projection. -/
def reductionProjectiveEmbedding (f : X ⟶ S) (g : Y ⟶ S) {d : ℕ}
    (e : Y ⟶ relativeSpace S d) (he : e ≫ relativeStructure S d = g) :
    reducedPullback f g ⟶ relativeSpace X d :=
  reductionι f g ≫ AlterationDominatingBaseChange.baseChangeEmbedding f g e he

instance reductionProjectiveEmbedding_isClosedImmersion (f : X ⟶ S) (g : Y ⟶ S) {d : ℕ}
    (e : Y ⟶ relativeSpace S d) [IsClosedImmersion e]
    (he : e ≫ relativeStructure S d = g) :
    IsClosedImmersion (reductionProjectiveEmbedding f g e he) := by
  unfold reductionProjectiveEmbedding
  infer_instance

@[reassoc (attr := simp)]
theorem reductionProjectiveEmbedding_structure (f : X ⟶ S) (g : Y ⟶ S) {d : ℕ}
    (e : Y ⟶ relativeSpace S d) (he : e ≫ relativeStructure S d = g) :
    reductionProjectiveEmbedding f g e he ≫ relativeStructure X d =
      reductionι f g ≫ pullback.fst f g := by
  simp [reductionProjectiveEmbedding]

end Hironaka.Geometry.CurveFibrationBaseChange
