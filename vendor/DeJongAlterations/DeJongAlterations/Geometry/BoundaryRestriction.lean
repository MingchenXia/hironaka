import DeJongAlterations.Theorem
import DeJongAlterations.Geometry.AlterationRestriction
import DeJongAlterations.Geometry.GenericallyEtaleComposition
import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Restriction of the actual full boundary output to a nonempty open

This is the conditional transport in de Jong 4.7. The actual compactification
and its full strict-normal-crossings ideal are retained. No compactification
existence theorem is asserted here.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace DeJongAlterations

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Geometry.BoundaryRestriction

/-- Shrinking an injective open image changes only the complement part of
the same boundary when the discarded points already belong to the boundary. -/
theorem boundary_image_identity {Y C : Type u} (i : Y → C) (hi : Function.Injective i)
    (A V : Set Y) (hV : Vᶜ ⊆ A) :
    i '' A ∪ (Set.range i)ᶜ = i '' (A ∩ V) ∪ (i '' V)ᶜ := by
  ext c
  constructor
  · rintro (⟨y, hy, rfl⟩ | hc)
    · by_cases hyV : y ∈ V
      · exact Or.inl ⟨y, ⟨hy, hyV⟩, rfl⟩
      · right
        rintro ⟨z, hz, hzi⟩
        exact hyV ((hi hzi) ▸ hz)
    · exact Or.inr fun ⟨y, _, hy⟩ => hc ⟨y, hy⟩
  · rintro (⟨y, hy, rfl⟩ | hc)
    · exact Or.inl ⟨y, hy.1, rfl⟩
    · by_cases hci : c ∈ Set.range i
      · obtain ⟨y, rfl⟩ := hci
        exact Or.inl ⟨y, hV (fun hyV => hc ⟨y, hyV, rfl⟩), rfl⟩
      · exact Or.inr hci

/-- A nonempty actual open subscheme of a variety is a variety over the
same field, with quasi-compactness derived from its original Noetherian source. -/
theorem open_variety {k : Type u} [Field k] {Y : Scheme.{u}}
    (q : Y ⟶ Spec (.of k)) [IsVariety q] (V : Y.Opens) [Nonempty V] :
    IsVariety (V.ι ≫ q) := by
  let : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian q
  let : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace q
  let : AlgebraicGeometry.IsNoetherian Y := ⟨⟩
  exact .mk

end Geometry.BoundaryRestriction

/-- Generic étaleness restricts to every actual target open. No integrality
or nonemptiness assumptions are needed for the dense-source-open witness. -/
theorem IsGenericallyEtale.morphismRestrict {X Y : Scheme.{u}} {f : X ⟶ Y}
    (hf : IsGenericallyEtale f) (U : Y.Opens) : IsGenericallyEtale (f ∣_ U) := by
  have hcomp : IsGenericallyEtale ((f ∣_ U) ≫ U.ι) := by
    rw [morphismRestrict_ι]
    exact (isGenericallyEtale_of_etale (f ⁻¹ᵁ U).ι).comp hf
  obtain ⟨V, hV, hEt⟩ := hcomp
  refine ⟨V, hV, ?_⟩
  let : Etale ((V.ι ≫ (f ∣_ U)) ≫ U.ι) := by
    simpa only [Category.assoc] using hEt
  exact Etale.of_comp (V.ι ≫ (f ∣_ U)) U.ι

variable {k : Type u} [Field k] {X : Scheme.{u}}

namespace Geometry.BoundaryRestriction

private theorem restriction_boundary_support {p : X ⟶ Spec (.of k)} {Z : Set X}
    (d : AlterationWithBoundary p Z) (U : X.Opens) (hU : (U : Set X)ᶜ ⊆ Z) :
    (d.boundary.support : Set d.compactification) =
      ((d.alteration ⁻¹ᵁ U).ι ≫ d.inclusion) ''
        ((d.alteration ∣_ U) ⁻¹' (U.ι ⁻¹' Z)) ∪
          (Set.range ((d.alteration ⁻¹ᵁ U).ι ≫ d.inclusion))ᶜ := by
  let : IsOpenImmersion d.inclusion := d.isOpenImmersion
  let V := d.alteration ⁻¹ᵁ U
  have hdiscard : (V : Set d.source)ᶜ ⊆ d.alteration ⁻¹' Z := by
    intro y hy
    exact hU hy
  have himg : V.ι '' ((d.alteration ∣_ U) ⁻¹' (U.ι ⁻¹' Z)) =
      (d.alteration ⁻¹' Z) ∩ (V : Set d.source) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨?_, x.property⟩
      simpa only [Set.mem_preimage, Scheme.Opens.ι_apply, morphismRestrict_base_coe] using hx
    · intro hy
      refine ⟨⟨y, hy.2⟩, ?_, rfl⟩
      simpa only [Set.mem_preimage, Scheme.Opens.ι_apply, morphismRestrict_base_coe] using hy.1
  rw [d.boundarySupport]
  calc
    d.inclusion '' (d.alteration ⁻¹' Z) ∪ (Set.range d.inclusion)ᶜ =
        d.inclusion '' ((d.alteration ⁻¹' Z) ∩ (V : Set d.source)) ∪
          (d.inclusion '' (V : Set d.source))ᶜ :=
      boundary_image_identity d.inclusion d.inclusion.isOpenEmbedding.injective
        (d.alteration ⁻¹' Z) V hdiscard
    _ = _ := by
      have hnewImage : ((V.ι ≫ d.inclusion) ''
          ((d.alteration ∣_ U) ⁻¹' (U.ι ⁻¹' Z))) =
          d.inclusion '' ((d.alteration ⁻¹' Z) ∩ (V : Set d.source)) := by
        calc
          _ = d.inclusion '' (V.ι '' ((d.alteration ∣_ U) ⁻¹' (U.ι ⁻¹' Z))) :=
            (Set.image_image d.inclusion V.ι _).symm
          _ = _ := by rw [himg]
      have hnewRange : Set.range (V.ι ≫ d.inclusion) =
          d.inclusion '' (V : Set d.source) := by
        calc
          _ = d.inclusion '' Set.range V.ι := Set.range_comp d.inclusion V.ι
          _ = _ := by rw [Scheme.Opens.range_ι]
      rw [hnewImage, hnewRange]

end Geometry.BoundaryRestriction

/-- The full conditional transport in de Jong 4.7. The source is the actual
inverse-image open; compactification, coefficient map and full boundary ideal
are retained exactly. The original boundary must contain the discarded base. -/
@[simps! source compactification sourceStructure compactificationStructure alteration inclusion boundary]
def AlterationWithBoundary.restrict {p : X ⟶ Spec (.of k)} {Z : Set X}
    (d : AlterationWithBoundary p Z) (U : X.Opens) [Nonempty U]
    (hU : (U : Set X)ᶜ ⊆ Z) : AlterationWithBoundary (U.ι ≫ p) (U.ι ⁻¹' Z) where
  source := (d.alteration ⁻¹ᵁ U).toScheme
  compactification := d.compactification
  sourceStructure := (d.alteration ⁻¹ᵁ U).ι ≫ d.sourceStructure
  compactificationStructure := d.compactificationStructure
  alteration := d.alteration ∣_ U
  inclusion := (d.alteration ⁻¹ᵁ U).ι ≫ d.inclusion
  boundary := d.boundary
  sourceVariety := by
    let := d.sourceVariety
    let := d.isAlteration
    let hr := IsAlteration.morphismRestrict d.alteration U
    let : IsIntegral (d.alteration ⁻¹ᵁ U).toScheme := hr.sourceIntegral
    exact Geometry.BoundaryRestriction.open_variety d.sourceStructure (d.alteration ⁻¹ᵁ U)
  compactificationVariety := d.compactificationVariety
  alterationOver := by
    rw [← Category.assoc, morphismRestrict_ι, Category.assoc, d.alterationOver]
  inclusionOver := by rw [Category.assoc, d.inclusionOver]
  isAlteration := by
    let := d.isAlteration
    exact IsAlteration.morphismRestrict d.alteration U
  isOpenImmersion := by
    let := d.isOpenImmersion
    infer_instance
  projective := d.projective
  regular := d.regular
  normalCrossings := d.normalCrossings
  boundarySupport := Geometry.BoundaryRestriction.restriction_boundary_support d U hU

/-- The actual restricted alteration preserves the dense-source generic
étaleness witness via native target-open restriction. -/
theorem AlterationWithBoundary.restrict_genericallyEtale
    {p : X ⟶ Spec (.of k)} {Z : Set X} (d : AlterationWithBoundary p Z)
    (U : X.Opens) [Nonempty U] (hU : (U : Set X)ᶜ ⊆ Z)
    (hd : IsGenericallyEtale d.alteration) :
    IsGenericallyEtale (d.restrict U hU).alteration := hd.morphismRestrict U

/-- The exact same compactification structure map retains its original
smoothness proof, together with generic étaleness of the actual restricted map. -/
theorem AlterationWithBoundary.restrict_perfectRefinement
    {p : X ⟶ Spec (.of k)} {Z : Set X} (d : AlterationWithBoundary p Z)
    (U : X.Opens) [Nonempty U] (hU : (U : Set X)ᶜ ⊆ Z)
    (hd : IsGenericallyEtale d.alteration) (hs : Smooth d.compactificationStructure) :
    IsGenericallyEtale (d.restrict U hU).alteration ∧
      Smooth (d.restrict U hU).compactificationStructure :=
  ⟨d.restrict_genericallyEtale U hU hd, hs⟩

end DeJongAlterations
