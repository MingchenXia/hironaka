import Hironaka.Analytic.Unibranch.Resolution
import Hironaka.Resolution.HironakaG10ChowOpenHomeomorph

/-!
# Isomorphism criteria for morphisms of reduced complex spaces

Native steps of the Chow-side lemma `chow:flat-bimeromorphic-iso`
(blueprint `hironaka-g10-chowside-flat-iso.tex`), in the original category
`SourceReducedComplexSpace` of reduced Hausdorff paracompact complex spaces.

Main declarations:

* `isIso_of_isHomeomorph_of_isIso_stalkMap` — a morphism whose point map is a
  homeomorphism and whose stalk maps are all isomorphisms is an isomorphism.
* `isIso_stalkMap_of_isIsoOver` — a morphism which is an isomorphism over `U` has
  bijective stalk maps at every point over `U`.
* `injOn_of_isIsoOver`, `subset_range_of_isIsoOver` — the point map is injective over
  `U` and covers `U`.
* `isHomeomorph_of_isProperBimeromorphic_of_isOpenMap` — **an open proper bimeromorphic
  morphism is a homeomorphism** (no dimension theory).
* `isIso_of_isProperBimeromorphic_of_isOpenMap` — an open proper bimeromorphic morphism
  whose stalk maps over the exceptional locus are isomorphisms is an isomorphism.
-/

set_option autoImplicit false

open Set TopologicalSpace CategoryTheory AlgebraicGeometry

namespace Hironaka.Analytic.Unibranch.HironakaG10ChowNativeIsoCriterion

open SourceReducedComplexSpace Hironaka.HironakaG10ChowOpenHomeomorph

noncomputable section

variable {X Y : SourceReducedComplexSpace}

/-- **Native isomorphism criterion.**  A morphism of reduced complex spaces whose point map
is a homeomorphism and whose stalk maps are isomorphisms is an isomorphism. -/
theorem isIso_of_isHomeomorph_of_isIso_stalkMap (p : Y ⟶ X)
    (hp : IsHomeomorph p.hom.left.base)
    (hs : ∀ y : Y.obj.left, IsIso (p.hom.left.stalkMap y)) : IsIso p := by
  have hoi : LocallyRingedSpace.IsOpenImmersion p.hom.left :=
    LocallyRingedSpace.IsOpenImmersion.of_stalk_iso _ hp.isOpenEmbedding (stalk_iso := hs)
  have hepi : Epi p.hom.left.base := (TopCat.epi_iff_surjective _).mpr hp.surjective
  have hleft : IsIso p.hom.left := LocallyRingedSpace.IsOpenImmersion.to_iso p.hom.left
  have : IsIso ((Over.forget _).map p.hom) := hleft
  have hover : IsIso p.hom := isIso_of_reflects_iso p.hom (Over.forget _)
  have : IsIso ((ObjectProperty.ι _).map p) := hover
  exact isIso_of_reflects_iso p (ObjectProperty.ι _)

/-- The point map of a morphism which is an isomorphism over `U` covers `U`. -/
theorem subset_range_of_isIsoOver {p : Y ⟶ X} {U : Set X.obj.left} (h : IsIsoOver p U) :
    U ⊆ range p.hom.left.base := by
  obtain ⟨V, j, _hj, _hr, _hjp, hr'⟩ := h
  intro x hx
  rw [← hr'] at hx
  obtain ⟨v, rfl⟩ := hx
  exact ⟨j.base v, rfl⟩

/-- The point map of a morphism which is an isomorphism over `U` is injective over `U`. -/
theorem injOn_of_isIsoOver {p : Y ⟶ X} {U : Set X.obj.left} (h : IsIsoOver p U) :
    InjOn p.hom.left.base (p.hom.left.base ⁻¹' U) := by
  obtain ⟨V, j, _hj, hr, hjp, _hr'⟩ := h
  intro y₁ hy₁ y₂ hy₂ heq
  rw [← hr] at hy₁ hy₂
  obtain ⟨v₁, rfl⟩ := hy₁
  obtain ⟨v₂, rfl⟩ := hy₂
  have hv : (j ≫ p.hom.left).base v₁ = (j ≫ p.hom.left).base v₂ := heq
  rw [hjp.base_open.injective hv]

/-- **Stalks over the good locus.**  If `p` is an isomorphism over `U`, its stalk map at
every point over `U` is an isomorphism. -/
theorem isIso_stalkMap_of_isIsoOver {p : Y ⟶ X} {U : Set X.obj.left} (h : IsIsoOver p U)
    (y : Y.obj.left) (hy : p.hom.left.base y ∈ U) : IsIso (p.hom.left.stalkMap y) := by
  obtain ⟨V, j, hj, hr, hjp, _hr'⟩ := h
  have hy' : y ∈ range j.base := by
    rw [hr]
    exact hy
  obtain ⟨v, rfl⟩ := hy'
  have hcomp : IsIso ((j ≫ p.hom.left).stalkMap v) := inferInstance
  rw [LocallyRingedSpace.stalkMap_comp] at hcomp
  have hjs : IsIso (j.stalkMap v) := inferInstance
  exact @IsIso.of_isIso_comp_right _ _ _ _ _ (p.hom.left.stalkMap (j.base v)) (j.stalkMap v) hjs hcomp

/-- **An open proper bimeromorphic morphism is a homeomorphism.**  If `p` is proper,
an isomorphism over the complement of a nowhere dense set, and its point map is open,
then its point map is a homeomorphism.  Two points of one fibre would have disjoint
neighbourhoods with open images meeting in the dense good locus, where `p` is
injective; the image is closed and contains the dense good locus. -/
theorem isHomeomorph_of_isProperBimeromorphic_of_isOpenMap {p : Y ⟶ X}
    (hp : IsProperBimeromorphic p) (ho : IsOpenMap p.hom.left.base) :
    IsHomeomorph p.hom.left.base := by
  obtain ⟨hproper, Z, _hZa, hZt, _hpre, hiso⟩ := hp
  have : T2Space Y.obj.left.toPresheafedSpace := Y.property.1
  have hdense : Dense Zᶜ := interior_eq_empty_iff_dense_compl.mp hZt
  exact isHomeomorph_of_isOpenMap_of_isProperMap ho hproper hdense (injOn_of_isIsoOver hiso)
    (subset_range_of_isIsoOver hiso)

/-- **Reduction of the flat-bimeromorphic isomorphism lemma to stalks over the exceptional
locus.**  An open proper bimeromorphic morphism, isomorphism over `Zᶜ`, whose stalk maps at
the points over `Z` are isomorphisms, is an isomorphism. -/
theorem isIso_of_isOpenMap_of_isIsoOver {p : Y ⟶ X} (hproper : IsProperMap p.hom.left.base)
    {Z : Set X.obj.left} (hZt : interior Z = ∅) (hiso : IsIsoOver p Zᶜ)
    (ho : IsOpenMap p.hom.left.base)
    (hs : ∀ y : Y.obj.left, p.hom.left.base y ∈ Z → IsIso (p.hom.left.stalkMap y)) :
    IsIso p := by
  have : T2Space Y.obj.left.toPresheafedSpace := Y.property.1
  have hdense : Dense Zᶜ := interior_eq_empty_iff_dense_compl.mp hZt
  refine isIso_of_isHomeomorph_of_isIso_stalkMap p
    (isHomeomorph_of_isOpenMap_of_isProperMap ho hproper hdense (injOn_of_isIsoOver hiso)
      (subset_range_of_isIsoOver hiso)) fun y => ?_
  by_cases hy : p.hom.left.base y ∈ Z
  · exact hs y hy
  · exact isIso_stalkMap_of_isIsoOver hiso y hy

/-- An open proper bimeromorphic morphism whose stalk maps are all isomorphisms is an
isomorphism. -/
theorem isIso_of_isProperBimeromorphic_of_isOpenMap {p : Y ⟶ X}
    (hp : IsProperBimeromorphic p) (ho : IsOpenMap p.hom.left.base)
    (hs : ∀ y : Y.obj.left, IsIso (p.hom.left.stalkMap y)) : IsIso p :=
  isIso_of_isHomeomorph_of_isIso_stalkMap p
    (isHomeomorph_of_isProperBimeromorphic_of_isOpenMap hp ho) hs

end

end Hironaka.Analytic.Unibranch.HironakaG10ChowNativeIsoCriterion
