import Hironaka.Geometry.CurveFibrationBaseChangeBoundaryEtale

/-!
# The actual whole reduced boundary is generically etale from paper hypotheses

All new source geometry and every boundary-component dominance hypothesis
are produced internally for the SAME whole-reduction model.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open Scheme.IdealSheafData
open Hironaka.Geometry.CartierBoundaryComponentDimension
open Hironaka.Geometry.CartierBoundaryDominance

namespace Hironaka.Geometry.CurveFibrationBaseChange

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {k : Type u} [Field k] {X S Y : Scheme.{u}}

/-- The WHOLE reduced inverse boundary is generically etale, with new component dominance derived internally. -/
theorem reducedBoundary_isGenericallyEtale_of_paper_fibres
    (p : S ⟶ Spec (.of k)) [IsVariety p] (f : X ⟶ S) [LocallyOfFinitePresentation f]
    [IsVariety (f ≫ p)] [IsProper f] [GeometricallyConnected f]
    [Smooth (f.fiberToSpecResidueField (genericPoint S))]
    (hsm : ∀ (K : Type u) [Field K] (a : Spec (.of K) ⟶ S),
      Dense ((pullback.fst f a) ⁻¹' (f.smoothLocus : Set X)))
    (hd : ∀ (K : Type u) [Field K] (a : Spec (.of K) ⟶ S)
      (C : Set (pullback f a : Scheme.{u})),
      C ∈ irreducibleComponents (pullback f a : Scheme.{u}) → topologicalKrullDim C = 1)
    (g : Y ⟶ S) [hg : IsAlteration g] (D : X.IdealSheafData)
    (hD : IsEffectiveCartierDivisor D)
    [IsFinite (reducedBoundaryInclusion D ≫ f)]
    (hDGE : IsGenericallyEtale (reducedBoundaryInclusion D ≫ f)) :
    IsGenericallyEtale (reducedBoundaryInclusion
      (D.comap (reductionι f g ≫ pullback.fst f g)) ≫
        (reductionι f g ≫ pullback.snd f g)) := by
  let : IsIntegral Y := hg.sourceIntegral
  let : IsLocallyNoetherian S := LocallyOfFiniteType.isLocallyNoetherian p
  let : CompactSpace S := QuasiCompact.compactSpace_of_compactSpace p
  let : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian g
  let : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace g
  let : AlgebraicGeometry.IsNoetherian Y := ⟨⟩
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (f ≫ p)
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (f ≫ p)
  let : AlgebraicGeometry.IsNoetherian X := ⟨⟩
  have hη := genericFiber_geometricallyIntegral_of_paper_fibres f
  let : IsIntegral (reducedPullback f g) := reducedPullback_isIntegral f hη hsm g
  let φ := reductionι f g ≫ pullback.fst f g
  let q := reductionι f g ≫ pullback.snd f g
  let E := D.comap φ
  let b := reducedBoundaryInclusion E ≫ q
  let : IsAlteration φ := reduction_first_isAlteration f g hη hsm
  let : GeometricallyConnected q := reducedSecond_geometricallyConnected f g
  let : IsProper q := by dsimp [q]; infer_instance
  let : IsVariety (g ≫ p) := .mk
  let : IsVariety (q ≫ (g ≫ p)) := .mk
  let : IsFinite b := reducedBoundary_isFinite f g D
  have hE : IsEffectiveCartierDivisor E :=
    CartierDominantPullback.isEffectiveCartierDivisor_comap φ D hD
  let : IsIntegral (q.fiber (genericPoint Y)) := GenericFiberIntegral.genericFiber_isIntegral q
  have hgen : topologicalKrullDim (q.fiber (genericPoint Y)) = 1 := by
    let a := Y.fromSpecResidueField (genericPoint Y)
    have hC : (Set.univ : Set (q.fiber (genericPoint Y))) ∈
        irreducibleComponents (q.fiber (genericPoint Y)) := by
      rw [irreducibleComponents_eq_singleton]
      exact Set.mem_singleton _
    have H := reducedSecond_fieldFiber_components_dimension f g 1 hd a Set.univ hC
    let e := Homeomorph.Set.univ (q.fiber (genericPoint Y))
    exact (IsHomeomorph.topologicalKrullDim_eq e e.isHomeomorph).symm.trans H
  let : ∀ C : DivisorComponent E, IsDominant (componentInclusion E C ≫ q) := fun C =>
    component_isDominant (g ≫ p) q hgen E hE C
  let B₀ := reducedBoundary D
  let b₀ := reducedBoundaryInclusion D ≫ f
  let : IsLocallyNoetherian B₀ := LocallyOfFiniteType.isLocallyNoetherian b₀
  let : CompactSpace B₀ := QuasiCompact.compactSpace_of_compactSpace b₀
  let : AlgebraicGeometry.IsNoetherian B₀ := ⟨⟩
  obtain ⟨V, hηV, _hV, hEt⟩ :=
    FiniteGenericallyEtaleOpen.exists_dense_target_etale_open b₀ hDGE
  let := hEt
  let U := g ⁻¹ᵁ V
  have hηU : genericPoint Y ∈ U := by
    change g (genericPoint Y) ∈ V
    rw [genericPoint_map_of_isDominant g]
    exact hηV
  let : Nonempty U := ⟨⟨genericPoint Y, hηU⟩⟩
  have hdense : Dense (b ⁻¹' (U : Set Y)) :=
    dense_reducedBoundary_preimage_of_componentDominant q E U hηU
  let : Etale (b ∣_ U) := reducedBoundary_etale_on_preimage f g D V
  refine ⟨b ⁻¹ᵁ U, hdense, ?_⟩
  rw [← morphismRestrict_ι]
  infer_instance

end Hironaka.Geometry.CurveFibrationBaseChange
