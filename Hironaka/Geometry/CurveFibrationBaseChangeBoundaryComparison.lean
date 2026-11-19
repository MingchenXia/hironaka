import Hironaka.Geometry.CurveFibrationBaseChangeBoundary

/-!
# An actual closed comparison for the same reduced inverse boundary

The map is constructed from the native closed-immersion universal property
and actual support computation. It is internally proved closed and surjective.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open Scheme.IdealSheafData

namespace Hironaka.Geometry.CurveFibrationBaseChange

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {X S Y N P T : Scheme.{u}}

/-- Actual reduced-source support containment gives the kernel containment needed for a native lift. -/
theorem kernel_le_of_reduced_range (c : P ⟶ T) [IsClosedImmersion c]
    (a : N ⟶ T) [IsReduced N] (h : Set.range a ⊆ Set.range c) : c.ker ≤ a.ker := by
  have hs : (c.ker.comap a).support = ⊤ := by
    rw [support_comap]
    ext x
    change a x ∈ (c.ker.support : Set T) ↔ True
    rw [Scheme.Hom.support_ker]
    exact ⟨fun _ => trivial, fun _ => subset_closure (h ⟨x, rfl⟩)⟩
  have hb : c.ker.comap a = ⊥ := Scheme.IdealSheafData.support_eq_top_iff.mp hs
  rw [← Scheme.IdealSheafData.map_bot a, Scheme.IdealSheafData.le_map_iff_comap_le]
  exact le_of_eq hb

/-- The actual original reduced-support boundary base change embeds into the original whole pullback. -/
def boundaryBaseChangeMap (f : X ⟶ S) (g : Y ⟶ S) (D : X.IdealSheafData) :
    pullback (CartierBoundaryDominance.reducedBoundaryInclusion D ≫ f) g ⟶ pullback f g :=
  pullback.map _ _ _ _ (CartierBoundaryDominance.reducedBoundaryInclusion D) (𝟙 Y) (𝟙 S)
    (by simp) (by simp)

instance boundaryBaseChangeMap_isClosedImmersion (f : X ⟶ S) (g : Y ⟶ S)
    (D : X.IdealSheafData) : IsClosedImmersion (boundaryBaseChangeMap f g D) :=
  MorphismProperty.pullbackMap (P := @IsClosedImmersion) inferInstance inferInstance (by simp) (by simp)

@[reassoc (attr := simp)]
theorem boundaryBaseChangeMap_fst (f : X ⟶ S) (g : Y ⟶ S) (D : X.IdealSheafData) :
    boundaryBaseChangeMap f g D ≫ pullback.fst f g =
      pullback.fst (CartierBoundaryDominance.reducedBoundaryInclusion D ≫ f) g ≫
        CartierBoundaryDominance.reducedBoundaryInclusion D := by
  simp [boundaryBaseChangeMap]

@[reassoc (attr := simp)]
theorem boundaryBaseChangeMap_snd (f : X ⟶ S) (g : Y ⟶ S) (D : X.IdealSheafData) :
    boundaryBaseChangeMap f g D ≫ pullback.snd f g =
      pullback.snd (CartierBoundaryDominance.reducedBoundaryInclusion D ≫ f) g := by
  simp [boundaryBaseChangeMap]

/-- The actual ordinary boundary base change has exactly its original inverse-support range. -/
theorem boundaryBaseChangeMap_range (f : X ⟶ S) (g : Y ⟶ S) (D : X.IdealSheafData) :
    Set.range (boundaryBaseChangeMap f g D) = (pullback.fst f g) ⁻¹' (D.support : Set X) := by
  have hr : Set.range (CartierBoundaryDominance.reducedBoundaryInclusion D) =
      (D.support : Set X) := by
    change Set.range (vanishingIdeal D.support).subschemeι = _
    rw [range_subschemeι]
    rfl
  simpa [boundaryBaseChangeMap, hr] using
    Scheme.Pullback.range_map (CartierBoundaryDominance.reducedBoundaryInclusion D ≫ f) g f g
      (CartierBoundaryDominance.reducedBoundaryInclusion D) (𝟙 Y) (𝟙 S) (by simp) (by simp)

/-- The actual native reduced boundary is reduced by its affine radical quotient construction. -/
instance reducedBoundary_isReduced (D : T.IdealSheafData) :
    IsReduced (CartierBoundaryDominance.reducedBoundary D) :=
  ReducedClosedSubscheme.isReduced_vanishingIdeal_subscheme D.support

/-- The SAME actual new reduced boundary lies in the original ordinary boundary base change. -/
theorem reducedBoundaryInclusion_range_le (f : X ⟶ S) (g : Y ⟶ S) (D : X.IdealSheafData) :
    Set.range (CartierBoundaryDominance.reducedBoundaryInclusion
      (D.comap (reductionι f g ≫ pullback.fst f g)) ≫ reductionι f g) ⊆
        Set.range (boundaryBaseChangeMap f g D) := by
  rw [boundaryBaseChangeMap_range]
  rintro _ ⟨z, rfl⟩
  let x : reducedPullback f g := z.val
  have hz : x ∈ (D.comap (reductionι f g ≫ pullback.fst f g)).support := z.property
  exact (congrArg (fun W : Closeds (reducedPullback f g) => x ∈ W)
    (support_comap D (reductionι f g ≫ pullback.fst f g))).mp hz

/-- Actual support computations construct the original map of the new reduced boundary to ordinary base change. -/
def reducedBoundaryComparison (f : X ⟶ S) (g : Y ⟶ S) (D : X.IdealSheafData) :
    CartierBoundaryDominance.reducedBoundary
      (D.comap (reductionι f g ≫ pullback.fst f g)) ⟶
        pullback (CartierBoundaryDominance.reducedBoundaryInclusion D ≫ f) g :=
  IsClosedImmersion.lift (boundaryBaseChangeMap f g D)
    (CartierBoundaryDominance.reducedBoundaryInclusion
      (D.comap (reductionι f g ≫ pullback.fst f g)) ≫ reductionι f g)
    (kernel_le_of_reduced_range _ _ (reducedBoundaryInclusion_range_le f g D))

@[reassoc (attr := simp)]
theorem reducedBoundaryComparison_structure (f : X ⟶ S) (g : Y ⟶ S) (D : X.IdealSheafData) :
    reducedBoundaryComparison f g D ≫ boundaryBaseChangeMap f g D =
      CartierBoundaryDominance.reducedBoundaryInclusion
        (D.comap (reductionι f g ≫ pullback.fst f g)) ≫ reductionι f g := by
  exact IsClosedImmersion.lift_fac _ _ _

instance reducedBoundaryComparison_isClosedImmersion (f : X ⟶ S) (g : Y ⟶ S)
    (D : X.IdealSheafData) : IsClosedImmersion (reducedBoundaryComparison f g D) := by
  have : IsClosedImmersion (reducedBoundaryComparison f g D ≫ boundaryBaseChangeMap f g D) := by
    rw [reducedBoundaryComparison_structure]
    infer_instance
  exact IsClosedImmersion.of_comp _ (boundaryBaseChangeMap f g D)

instance reducedBoundaryComparison_surjective (f : X ⟶ S) (g : Y ⟶ S)
    (D : X.IdealSheafData) : Surjective (reducedBoundaryComparison f g D) := by
  let E := D.comap (reductionι f g ≫ pullback.fst f g)
  let c := boundaryBaseChangeMap f g D
  refine ⟨?_⟩
  intro p
  obtain ⟨z, hz⟩ := (reductionι f g).surjective (c p)
  have hzE : z ∈ E.support := by
    rw [support_comap]
    change (reductionι f g ≫ pullback.fst f g) z ∈ D.support
    change pullback.fst f g (reductionι f g z) ∈ D.support
    rw [hz]
    have hcp : c p ∈ Set.range c := ⟨p, rfl⟩
    rw [boundaryBaseChangeMap_range] at hcp
    exact hcp
  let w : CartierBoundaryDominance.reducedBoundary E := ⟨z, hzE⟩
  refine ⟨w, c.isEmbedding.injective ?_⟩
  have H := congrArg (fun h => h w) (reducedBoundaryComparison_structure f g D)
  simpa only [Scheme.Hom.comp_apply, Scheme.IdealSheafData.subschemeι_apply] using H.trans hz

@[reassoc (attr := simp)]
theorem reducedBoundaryComparison_snd (f : X ⟶ S) (g : Y ⟶ S) (D : X.IdealSheafData) :
    reducedBoundaryComparison f g D ≫
      pullback.snd (CartierBoundaryDominance.reducedBoundaryInclusion D ≫ f) g =
    CartierBoundaryDominance.reducedBoundaryInclusion
      (D.comap (reductionι f g ≫ pullback.fst f g)) ≫
        (reductionι f g ≫ pullback.snd f g) := by
  rw [← boundaryBaseChangeMap_snd f g D, ← Category.assoc, reducedBoundaryComparison_structure,
    Category.assoc]

end Hironaka.Geometry.CurveFibrationBaseChange
