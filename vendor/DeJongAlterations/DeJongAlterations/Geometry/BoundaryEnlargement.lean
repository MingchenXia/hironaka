import DeJongAlterations.Geometry.BoundaryEnlargementBasic
import DeJongAlterations.Geometry.BoundaryEnlargementComponents
import DeJongAlterations.Geometry.CartierPureCodimension
import DeJongAlterations.Geometry.CartierDominantPullback

/-!
# De Jong 4.9: enlarging the actual closed boundary

Dominant pullback produces the actual Cartier ideal; actual purity and
native SNC component deletion produce its actual reduced SNC boundary.
The full output retains all source, alteration and compactification data.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace DeJongAlterations.Geometry.BoundaryEnlargement

open Scheme.IdealSheafData

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

variable {X : Scheme.{u}}

/-- A genuine Cartier support contained in native SNC has its actual reduced SNC structure. -/
theorem isStrictNormalCrossings_of_cartier_support_subset
    [IsIntegral X] [IsLocallyNoetherian X] [NoetherianSpace X]
    (E : X.IdealSheafData) (hE : IsEffectiveCartierDivisor E)
    (D : X.IdealSheafData) (hD : IsStrictNormalCrossings D) (hED : E.support ≤ D.support) :
    IsStrictNormalCrossings (vanishingIdeal E.support) :=
  isStrictNormalCrossings_of_pureCodimension_subset D hD E.support
    (CartierPureCodimension.hasPureCodimension E hE) hED

variable {k : Type u} [Field k] {p : X ⟶ Spec (.of k)}

/-- The actual inclusion isomorphism identifies arbitrary inverse-image boundaries exactly. -/
theorem inclusion_image_preimage [IsProper p] {Z : Set X}
    (d : AlterationWithBoundary p Z) (W : Set X) :
    d.inclusion '' (d.alteration ⁻¹' W) ∪ (Set.range d.inclusion)ᶜ =
      compactificationMap d ⁻¹' W := by
  let : IsIso d.inclusion := inclusion_isIso_of_isProper d
  have hsurj : Function.Surjective d.inclusion :=
    (Scheme.homeoOfIso (asIso d.inclusion)).surjective
  rw [Set.range_eq_univ.mpr hsurj, Set.compl_univ, Set.union_empty]
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    have h := congrArg (fun f : d.source ⟶ X ↦ f y) (inclusion_compactificationMap d)
    change compactificationMap d (d.inclusion y) ∈ W
    rw [show compactificationMap d (d.inclusion y) = d.alteration y from h]
    exact hy
  · intro hx
    refine ⟨inv d.inclusion x, hx, ?_⟩
    exact congrArg (fun f : d.compactification ⟶ d.compactification ↦ f x)
      (IsIso.inv_hom_id d.inclusion)

/-- De Jong 4.9: solve an enlarged closed boundary and construct the full output for the original Cartier support. -/
def shrinkBoundary [IsProper p]
    (E : X.IdealSheafData) (hE : IsEffectiveCartierDivisor E)
    (Z' : Closeds X) (hEZ' : E.support ≤ Z')
    (d : AlterationWithBoundary p (Z' : Set X)) :
    AlterationWithBoundary p (E.support : Set X) := by
  let : IsVariety d.compactificationStructure := d.compactificationVariety
  let : IsLocallyNoetherian d.compactification :=
    LocallyOfFiniteType.isLocallyNoetherian d.compactificationStructure
  let : CompactSpace d.compactification :=
    QuasiCompact.compactSpace_of_compactSpace d.compactificationStructure
  let : IsNoetherian d.compactification :=
    { toIsLocallyNoetherian := inferInstance, toCompactSpace := inferInstance }
  let g := compactificationMap d
  have hg : IsAlteration g := compactificationMap_isAlteration d
  let : IsAlteration g := hg
  let : IsIntegral X := hg.targetIntegral
  let : IsDominant g := inferInstance
  let E' := E.comap g
  have hE' : IsEffectiveCartierDivisor E' :=
    CartierDominantPullback.isEffectiveCartierDivisor_comap g E hE
  have hsubset : E'.support ≤ d.boundary.support := by
    intro y hy
    rw [support_comap] at hy
    change g y ∈ E.support at hy
    change y ∈ (d.boundary.support : Set d.compactification)
    rw [boundary_support_eq_preimage d]
    exact hEZ' hy
  have hsnc : IsStrictNormalCrossings (vanishingIdeal E'.support) :=
    isStrictNormalCrossings_of_cartier_support_subset E' hE' d.boundary d.normalCrossings hsubset
  refine { d with
    boundary := vanishingIdeal E'.support
    normalCrossings := hsnc
    boundarySupport := ?_ }
  change (E'.support : Set d.compactification) =
    d.inclusion '' (d.alteration ⁻¹' (E.support : Set X)) ∪ (Set.range d.inclusion)ᶜ
  rw [support_comap]
  exact (inclusion_image_preimage d (E.support : Set X)).symm

@[simp]
theorem shrinkBoundary_source [IsProper p]
    (E : X.IdealSheafData) (hE : IsEffectiveCartierDivisor E)
    (Z' : Closeds X) (hEZ' : E.support ≤ Z') (d : AlterationWithBoundary p (Z' : Set X)) :
    (shrinkBoundary E hE Z' hEZ' d).source = d.source := rfl

@[simp]
theorem shrinkBoundary_compactification [IsProper p]
    (E : X.IdealSheafData) (hE : IsEffectiveCartierDivisor E)
    (Z' : Closeds X) (hEZ' : E.support ≤ Z') (d : AlterationWithBoundary p (Z' : Set X)) :
    (shrinkBoundary E hE Z' hEZ' d).compactification = d.compactification := rfl

@[simp]
theorem shrinkBoundary_alteration [IsProper p]
    (E : X.IdealSheafData) (hE : IsEffectiveCartierDivisor E)
    (Z' : Closeds X) (hEZ' : E.support ≤ Z') (d : AlterationWithBoundary p (Z' : Set X)) :
    (shrinkBoundary E hE Z' hEZ' d).alteration = d.alteration := rfl

theorem shrinkBoundary_genericallyEtale [IsProper p]
    (E : X.IdealSheafData) (hE : IsEffectiveCartierDivisor E)
    (Z' : Closeds X) (hEZ' : E.support ≤ Z') (d : AlterationWithBoundary p (Z' : Set X))
    (hd : IsGenericallyEtale d.alteration) :
    IsGenericallyEtale (shrinkBoundary E hE Z' hEZ' d).alteration := hd

theorem shrinkBoundary_smooth [IsProper p]
    (E : X.IdealSheafData) (hE : IsEffectiveCartierDivisor E)
    (Z' : Closeds X) (hEZ' : E.support ≤ Z') (d : AlterationWithBoundary p (Z' : Set X))
    (hd : Smooth d.compactificationStructure) :
    Smooth (shrinkBoundary E hE Z' hEZ' d).compactificationStructure := hd

end DeJongAlterations.Geometry.BoundaryEnlargement
