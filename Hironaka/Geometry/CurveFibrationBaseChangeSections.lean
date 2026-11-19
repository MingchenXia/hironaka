import Hironaka.Geometry.CurveFibrationBaseChangePaperDensity
import Hironaka.Geometry.CartierBoundarySections

/-!
# Actual boundary sections on the SAME whole reduced pullback of source4.16

Internally construct the original boundary components' common Galois
normalization. Use the literal whole reduction, never an independently
chosen dominant component. Existing actual sections descend into it and
cover its complete pulled-back boundary support, without flatness.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open Hironaka.Geometry.RelativeChow

namespace Hironaka.Geometry.CurveFibrationBaseChange

open Scheme.IdealSheafData CartierBoundaryComponentDimension CartierBoundaryDominance
open CartierBoundarySection FiniteBirationalNormal

universe u

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {k : Type u} [Field k] {X S : Scheme.{u}}

/-- The generic fibre's single component computes its actual dimension from all field fibres. -/
theorem genericFiber_dimension_one_of_field_components
    (f : X ⟶ S) [IsIntegral S] [IsIntegral (f.fiber (genericPoint S))]
    (hd : ∀ (K : Type u) [Field K] (a : Spec (.of K) ⟶ S)
      (C : Set (pullback f a : Scheme.{u})),
      C ∈ irreducibleComponents (pullback f a : Scheme.{u}) → topologicalKrullDim C = 1) :
    topologicalKrullDim (f.fiber (genericPoint S)) = 1 := by
  let a := S.fromSpecResidueField (genericPoint S)
  have hC : (Set.univ : Set (f.fiber (genericPoint S))) ∈
      irreducibleComponents (f.fiber (genericPoint S)) := by
    rw [irreducibleComponents_eq_singleton]
    exact Set.mem_singleton _
  have H := hd _ a Set.univ hC
  let e := Homeomorph.Set.univ (f.fiber (genericPoint S))
  exact (IsHomeomorph.topologicalKrullDim_eq e e.isHomeomorph).symm.trans H

/-- The original boundary internally produces sections of the SAME literal whole reduced pullback. -/
theorem exists_wholeReduction_boundary_sections
    (p : S ⟶ Spec (.of k)) [IsVariety p] (hp : IsProjectiveOver p)
    (f : X ⟶ S) [IsVariety (f ≫ p)] [LocallyOfFinitePresentation f] [IsProper f]
    [GeometricallyConnected f] [Smooth (f.fiberToSpecResidueField (genericPoint S))]
    (hsm : ∀ s : S, Dense ((f.fiberι s) ⁻¹' (f.smoothLocus : Set X)))
    (hd : ∀ (K : Type u) [Field K] (a : Spec (.of K) ⟶ S)
      (C : Set (pullback f a : Scheme.{u})),
      C ∈ irreducibleComponents (pullback f a : Scheme.{u}) → topologicalKrullDim C = 1)
    (D : X.IdealSheafData) (hD : IsEffectiveCartierDivisor D)
    [IsFinite (reducedBoundaryInclusion D ≫ f)]
    (hGE : IsGenericallyEtale (reducedBoundaryInclusion D ≫ f)) :
    ∃ (Y : Scheme.{u}) (g : Y ⟶ S) (κ : Type u) (_ : Finite κ)
      (σ : κ → (Y ⟶ reducedPullback f g)),
      IsFinite g ∧ IsAlteration g ∧ IsGenericallyEtale g ∧ IsNormalScheme Y ∧
      IsVariety (g ≫ p) ∧ IsProjectiveOver (g ≫ p) ∧
      IsIntegral (reducedPullback f g) ∧
      (∀ a, σ a ≫ (reductionι f g ≫ pullback.snd f g) = 𝟙 Y ∧ IsClosedImmersion (σ a)) ∧
      ⋃ a, Set.range (σ a) =
        ((D.comap (reductionι f g ≫ pullback.fst f g)).support : Set (reducedPullback f g)) := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (f ≫ p)
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (f ≫ p)
  let : AlgebraicGeometry.IsNoetherian X := ⟨⟩
  let : IsLocallyNoetherian (reducedBoundary D) :=
    LocallyOfFiniteType.isLocallyNoetherian (reducedBoundaryInclusion D)
  let : CompactSpace (reducedBoundary D) :=
    QuasiCompact.compactSpace_of_compactSpace (reducedBoundaryInclusion D)
  let : AlgebraicGeometry.IsNoetherian (reducedBoundary D) := ⟨⟩
  let : Finite (DivisorComponent D) := divisorComponent_finite D
  let : IsIntegral (f.fiber (genericPoint S)) := GenericFiberIntegral.genericFiber_isIntegral f
  have hgen := genericFiber_dimension_one_of_field_components f hd
  let (C : DivisorComponent D) : IsDominant (componentInclusion D C ≫ f) :=
    component_isDominant p f hgen D hD C
  obtain ⟨L, hfinite, hG, he, hvar, hN, hfin, halt, hget, hproj, _⟩ :=
    exists_common_galois_normalization p hp (componentScheme D)
      (fun C => componentInclusion D C ≫ f) (component_genericallyEtale f D hGE)
  let := hfinite
  let := hG
  let Y := NormalizationInExtension.normalization S L
  let g := NormalizationInExtension.normalizationStructure S L
  let : IsFinite g := hfin
  let : IsAlteration g := halt
  let : IsIntegral Y := halt.sourceIntegral
  let : IsVariety (g ≫ p) := hvar
  have hη := genericFiber_geometricallyIntegral_of_paper_fibres f
  have hfield := fun (K : Type u) [Field K] (a : Spec (.of K) ⟶ S) =>
    original_smoothLocus_fieldFiber_dense f hsm a
  let : IsIntegral (reducedPullback f g) := reducedPullback_isIntegral f hη hfield g
  let q := reductionι f g ≫ pullback.snd f g
  let φ := reductionι f g ≫ pullback.fst f g
  let E := D.comap φ
  let : IsAlteration φ := reduction_first_isAlteration f g hη hfield
  let : GeometricallyConnected q := reducedSecond_geometricallyConnected f g
  let : IsVariety (q ≫ (g ≫ p)) := .mk
  let : IsFinite (reducedBoundaryInclusion E ≫ q) := reducedBoundary_isFinite f g D
  have hE : IsEffectiveCartierDivisor E :=
    CartierDominantPullback.isEffectiveCartierDivisor_comap φ D hD
  let : IsIntegral (q.fiber (genericPoint Y)) := GenericFiberIntegral.genericFiber_isIntegral q
  have hqd : ∀ (K : Type u) [Field K] (a : Spec (.of K) ⟶ Y)
      (C : Set (pullback q a : Scheme.{u})),
      C ∈ irreducibleComponents (pullback q a : Scheme.{u}) → topologicalKrullDim C = 1 :=
    fun _ _ a C hC => reducedSecond_fieldFiber_components_dimension f g 1 hd a C hC
  have hqgen := genericFiber_dimension_one_of_field_components q hqd
  let (C : DivisorComponent E) : IsDominant (componentInclusion E C ≫ q) :=
    component_isDominant (g ≫ p) q hqgen E hE C
  let e : ∀ C : DivisorComponent D, ComponentEmbeddings f D L C := Classical.choice he
  let ι := Σ C : DivisorComponent D, ComponentEmbeddings f D L C
  let : Finite ι := finite_componentSectionIndex p f D L
  let s : ι → (Y ⟶ pullback f g) := fun i => ambientSection f D L i.1 i.2
  obtain ⟨κ, hκ, σ, hσ, hcover⟩ := exists_selected_sections
    (pullback.snd f g) (reductionι f g) E s (fun i => ambientSection_snd f D L i.1 i.2)
    (fun _ => inferInstance) (by
      intro i y t ht
      rw [support_comap]
      change pullback.fst f g (reductionι f g t) ∈ D.support
      rw [ht]
      exact ambientSection_mem_support f D L i.1 i.2 y) (by
      intro t ht htg
      have ht' : pullback.fst f g (reductionι f g t) ∈ D.support := by
        change t ∈ (D.comap (reductionι f g ≫ pullback.fst f g)).support at ht
        rw [support_comap] at ht
        exact ht
      obtain ⟨C, σ, hσ⟩ := ambientSection_generic_cover p f D L e (reductionι f g t) ht' htg
      exact ⟨⟨C, σ⟩, hσ⟩)
  exact ⟨Y, g, κ, hκ, σ, hfin, halt, hget, hN, hvar, hproj, inferInstance, hσ, hcover⟩

end Hironaka.Geometry.CurveFibrationBaseChange
