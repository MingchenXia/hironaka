import Hironaka.Geometry.CurveFibrationBaseChangeSmooth
import Hironaka.Geometry.CurveFibrationBaseChangeFibers
import Hironaka.Geometry.CartierBoundaryFiniteBaseChange

/-!
# Actual reduced-boundary finiteness and geometric three-point transport

All points and components are on actual native field fibres, and the
same whole-reduction map retains the original boundary coordinates.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace Hironaka.Geometry.CurveFibrationBaseChange

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {X S Y : Scheme.{u}}

/-- The actual canonical field-fibre homeomorphism retains its original X-coordinate. -/
theorem reducedFieldFiberHomeomorph_fst (f : X ⟶ S) (g : Y ⟶ S)
    {K : Type u} [Field K] (a : Spec (.of K) ⟶ Y)
    (z : (pullback (reductionι f g ≫ pullback.snd f g) a : Scheme.{u})) :
    pullback.fst f (a ≫ g) (reducedFieldFiberHomeomorph f g a z) =
      (pullback.fst (reductionι f g ≫ pullback.snd f g) a ≫
        reductionι f g ≫ pullback.fst f g) z := by
  change (reductionBaseChangeMap f g a ≫ (wholeFieldFiberIso f g a).hom ≫
    pullback.fst f (a ≫ g)) z = _
  simp [wholeFieldFiberIso, reductionBaseChangeMap]

/-- Every actual component is taken to an actual original component by the SAME field-fibre comparison. -/
theorem reducedFieldFiberHomeomorph_image_component (f : X ⟶ S) (g : Y ⟶ S)
    {K : Type u} [Field K] (a : Spec (.of K) ⟶ Y)
    (C : Set (pullback (reductionι f g ≫ pullback.snd f g) a : Scheme.{u}))
    (hC : C ∈ irreducibleComponents
      (pullback (reductionι f g ≫ pullback.snd f g) a : Scheme.{u})) :
    (reducedFieldFiberHomeomorph f g a) '' C ∈ irreducibleComponents
      (pullback f (a ≫ g) : Scheme.{u}) := by
  let h := reducedFieldFiberHomeomorph f g a
  rw [h.image_eq_preimage_symm]
  exact preimage_mem_irreducibleComponents hC h.symm.isOpenEmbedding (by
    simpa only [h.symm.surjective.range_eq, Set.inter_univ] using hC.1.nonempty)

/-- Finiteness of the original actual reduced boundary gives finiteness of the SAME new reduced boundary. -/
theorem reducedBoundary_isFinite (f : X ⟶ S) (g : Y ⟶ S) (D : X.IdealSheafData)
    [IsFinite (CartierBoundaryDominance.reducedBoundaryInclusion D ≫ f)] :
    IsFinite (CartierBoundaryDominance.reducedBoundaryInclusion
      (D.comap (reductionι f g ≫ pullback.fst f g)) ≫
        (reductionι f g ≫ pullback.snd f g)) :=
  CartierBoundaryDominance.reducedBoundary_isFinite_of_closed_baseChange f g D (reductionι f g)


/-- The original three distinct geometric smooth-boundary points survive on EVERY actual new component. -/
theorem reducedSecond_three_geometric_points [IsIntegral Y] [IsLocallyNoetherian Y]
    (f : X ⟶ S) [LocallyOfFinitePresentation f] (g : Y ⟶ S) (D : X.IdealSheafData)
    (hthree : ∀ (K : Type u) [Field K] [IsAlgClosed K] (a : Spec (.of K) ⟶ S)
      (C : Set (pullback f a : Scheme.{u})),
      C ∈ irreducibleComponents (pullback f a : Scheme.{u}) →
      ∃ v : Fin 3 → (pullback f a : Scheme.{u}), Function.Injective v ∧ ∀ i,
        v i ∈ C ∧ pullback.fst f a (v i) ∈ f.smoothLocus ∧
          pullback.fst f a (v i) ∈ D.support) :
    ∀ (K : Type u) [Field K] [IsAlgClosed K] (a : Spec (.of K) ⟶ Y)
      (C : Set (pullback (reductionι f g ≫ pullback.snd f g) a : Scheme.{u})),
      C ∈ irreducibleComponents
        (pullback (reductionι f g ≫ pullback.snd f g) a : Scheme.{u}) →
      ∃ v : Fin 3 → (pullback (reductionι f g ≫ pullback.snd f g) a : Scheme.{u}),
        Function.Injective v ∧ ∀ i, v i ∈ C ∧
          pullback.fst (reductionι f g ≫ pullback.snd f g) a (v i) ∈
            (reductionι f g ≫ pullback.snd f g).smoothLocus ∧
          pullback.fst (reductionι f g ≫ pullback.snd f g) a (v i) ∈
            (D.comap (reductionι f g ≫ pullback.fst f g)).support := by
  intro K _ _ a C hC
  let q := reductionι f g ≫ pullback.snd f g
  let h := reducedFieldFiberHomeomorph f g a
  obtain ⟨v, hvinj, hv⟩ := hthree K (a ≫ g) (h '' C)
    (reducedFieldFiberHomeomorph_image_component f g a C hC)
  let w : Fin 3 → (pullback q a : Scheme.{u}) := fun i => h.symm (v i)
  refine ⟨w, h.symm.injective.comp hvinj, ?_⟩
  intro i
  have hwi : w i ∈ C := by
    obtain ⟨z, hzC, hzv⟩ := (hv i).1
    change h.symm (v i) ∈ C
    rw [← hzv, h.symm_apply_apply]
    exact hzC
  have hwX : pullback.fst f (a ≫ g) (v i) =
      (pullback.fst q a ≫ reductionι f g ≫ pullback.fst f g) (w i) := by
    have H := reducedFieldFiberHomeomorph_fst f g a (w i)
    change pullback.fst f (a ≫ g) (h (h.symm (v i))) = _ at H
    simpa only [h.apply_symm_apply] using H
  have hwiSm : pullback.fst q a (w i) ∈
      (reductionι f g) ⁻¹ᵁ ((pullback.fst f g) ⁻¹ᵁ f.smoothLocus) := by
    change (pullback.fst q a ≫ reductionι f g ≫ pullback.fst f g) (w i) ∈ f.smoothLocus
    rw [← hwX]
    exact (hv i).2.1
  refine ⟨hwi, originalLocus_le_reduced_smoothLocus f g hwiSm, ?_⟩
  rw [Scheme.IdealSheafData.support_comap]
  change (pullback.fst q a ≫ reductionι f g ≫ pullback.fst f g) (w i) ∈ D.support
  rw [← hwX]
  exact (hv i).2.2

end Hironaka.Geometry.CurveFibrationBaseChange
