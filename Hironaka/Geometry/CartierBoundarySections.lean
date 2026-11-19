import Hironaka.Geometry.CartierBoundarySectionGeneric
import Hironaka.Geometry.CartierBoundarySectionCoverage

/-!
# Actual nonflat Cartier boundary sections on the internally constructed model

This is the section conclusion of source 4.16 for varieties over a field.
The common Galois field is constructed from the original boundary
components. Both the finite normal base change and the reduced dominant
component model are internal. No boundary flatness or post-base-change
component dominance is assumed. All-fibre conditions of source 4.15 and
normalization over arbitrary excellent bases are separate assertions.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace Hironaka.Geometry.CartierBoundarySection

open Scheme.IdealSheafData CartierBoundaryComponentDimension CartierBoundaryDominance
open FiniteBirationalNormal

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {k : Type u} [Field k] {X S : Scheme.{u}}

/-- The entire actual Cartier boundary on an internally constructed finite base-change
component is a finite union of genuine closed sections. The common Galois field, normal
projective base alteration, actual reduced component, component dominance and section maps
are all constructed internally from the original finite generically-etale boundary. -/
theorem exists_alteration_boundary_sections
    (p : S ⟶ Spec (.of k)) [IsVariety p] (hp : IsProjectiveOver p)
    (f : X ⟶ S) [IsVariety (f ≫ p)] [IsDominant f]
    (hgen : topologicalKrullDim (f.fiber (genericPoint S)) = 1)
    (D : X.IdealSheafData) (hD : IsEffectiveCartierDivisor D)
    [IsFinite (reducedBoundaryInclusion D ≫ f)]
    (hGE : IsGenericallyEtale (reducedBoundaryInclusion D ≫ f)) :
    ∃ (Y : Scheme.{u}) (g : Y ⟶ S) (T : Scheme.{u}) (j : T ⟶ pullback f g)
      (κ : Type u) (_ : Finite κ) (σ : κ → (Y ⟶ T)),
      IsFinite g ∧ IsAlteration g ∧ IsGenericallyEtale g ∧ IsNormalScheme Y ∧
      IsVariety (g ≫ p) ∧ IsProjectiveOver (g ≫ p) ∧
      IsIntegral T ∧ IsClosedImmersion j ∧
      Set.range j ∈ irreducibleComponents (pullback f g : Scheme.{u}) ∧
      IsDominant (j ≫ pullback.fst f g) ∧ IsDominant (j ≫ pullback.snd f g) ∧
      IsAlteration (j ≫ pullback.fst f g) ∧
      IsEffectiveCartierDivisor (D.comap (j ≫ pullback.fst f g)) ∧
      IsFinite (reducedBoundaryInclusion (D.comap (j ≫ pullback.fst f g)) ≫
        (j ≫ pullback.snd f g)) ∧
      (∀ a, σ a ≫ (j ≫ pullback.snd f g) = 𝟙 Y ∧ IsClosedImmersion (σ a)) ∧
      ⋃ a, Set.range (σ a) = ((D.comap (j ≫ pullback.fst f g)).support : Set T) := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (f ≫ p)
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (f ≫ p)
  let : AlgebraicGeometry.IsNoetherian X := ⟨⟩
  let : IsLocallyNoetherian (reducedBoundary D) :=
    LocallyOfFiniteType.isLocallyNoetherian (reducedBoundaryInclusion D)
  let : CompactSpace (reducedBoundary D) :=
    QuasiCompact.compactSpace_of_compactSpace (reducedBoundaryInclusion D)
  let : AlgebraicGeometry.IsNoetherian (reducedBoundary D) := ⟨⟩
  let : Finite (DivisorComponent D) := divisorComponent_finite D
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
  let : IsVariety (g ≫ p) := hvar
  let : IsDominant g := halt.toIsDominant
  let e : ∀ C : DivisorComponent D, ComponentEmbeddings f D L C := Classical.choice he
  obtain ⟨T, j, hT, hj, hjcomp, hq, hb, hqa, hE, hEf, hCdom⟩ :=
    exists_finite_baseChange_model_boundary_dominant p f hgen D hD g
  let := hT
  let := hj
  let E := D.comap (j ≫ pullback.fst f g)
  let (C : DivisorComponent E) :
      IsDominant (componentInclusion E C ≫ (j ≫ pullback.snd f g)) := hCdom C
  let ι := Σ C : DivisorComponent D, ComponentEmbeddings f D L C
  let : Finite ι := finite_componentSectionIndex p f D L
  let s : ι → (Y ⟶ pullback f g) := fun i => ambientSection f D L i.1 i.2
  obtain ⟨κ, hκ, σ, hσ, hcover⟩ := exists_selected_sections
    (pullback.snd f g) j E s (fun i => ambientSection_snd f D L i.1 i.2)
    (fun _ => inferInstance) (by
      intro i y t ht
      rw [support_comap]
      change pullback.fst f g (j t) ∈ D.support
      rw [ht]
      exact ambientSection_mem_support f D L i.1 i.2 y) (by
      intro t ht htg
      have ht' : pullback.fst f g (j t) ∈ D.support := by
        change t ∈ (D.comap (j ≫ pullback.fst f g)).support at ht
        rw [support_comap] at ht
        exact ht
      obtain ⟨C, σ, hσ⟩ := ambientSection_generic_cover p f D L e (j t) ht' htg
      exact ⟨⟨C, σ⟩, hσ⟩)
  exact ⟨Y, g, T, j, κ, hκ, σ, hfin, halt, hget, hN, hvar, hproj,
    hT, hj, hjcomp, hq, hb, hqa, hE, hEf, hσ, hcover⟩

end Hironaka.Geometry.CartierBoundarySection
