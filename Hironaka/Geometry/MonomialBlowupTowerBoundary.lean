import Hironaka.Geometry.MonomialBlowupTowerBoundaryFinished
import Hironaka.Geometry.MonomialBlowupTowerBoundaryCover

/-!
# SNC of the actual reduced total boundary of any finite coordinate-node tower

The original monomial and its multiplicities are retained in the total
inverse-image ideal. Its actual radical is identified on the actual global
finished-node cover; no chart SNC or component certificates are inputs.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MvPolynomial

namespace Hironaka.Geometry.MonomialBlowupTowerBoundary

open Algebra.NodeBlowupChart SpecIdealSheaf CoordinateSNC
open MonomialBlowupTower MonomialBlowupTowerBoundaryPolynomial
open MonomialBlowupTowerBoundaryFinished MonomialBlowupTowerBoundaryCover

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (K : Type u) [Field K] {ι : Type u} [DecidableEq ι] [Finite ι]

/-- The actual factor list in the polynomial coefficient ring. -/
def factors (l : List ι) : List (Base K (ι := ι)) := l.map (fun i ↦ X i)

/-- The original monomial ideal on the actual polynomial base, with all multiplicities. -/
def baseRawBoundary (l : List ι) :
    (Spec (CommRingCat.of (Base K (ι := ι)))).IdealSheafData :=
  specIdealSheaf (Base K (ι := ι)) (Ideal.span {monomial K l})

/-- The actual coefficient inverse image on the original finite-product node. -/
def originalRawBoundary (l : List ι) : (original (factors K l)).IdealSheafData :=
  (baseRawBoundary K l).comap (nodeToBase (factors K l).prod)

/-- The actual total inverse image under the literal finite global blowup morphism. -/
def rawBoundary (l : List ι) : (resolved (factors K l)).IdealSheafData :=
  (originalRawBoundary K l).comap (resolutionMorphism (factors K l))

/-- The reduced total inverse-image ideal, on the actual final global tower. -/
def boundary (l : List ι) : (resolved (factors K l)).IdealSheafData :=
  (rawBoundary K l).radical

omit [DecidableEq ι] [Finite ι] in
/-- The actual reduced boundary retains precisely the original total inverse-image support. -/
theorem boundary_support (l : List ι) :
    (boundary K l).support = ((originalRawBoundary K l).support).preimage
      (resolutionMorphism (factors K l)).continuous := by
  rw [boundary, Scheme.IdealSheafData.support_radical, rawBoundary,
    Scheme.IdealSheafData.support_comap]

/-- Every genuine coordinate-node factor has the derived reduced SNC coefficient boundary. -/
theorem coefficientBoundary_isStrictNormalCrossings (l : List ι)
    (t : Base K (ι := ι)) (ht : t ∈ factors K l) :
    IsStrictNormalCrossings (((baseRawBoundary K l).comap (nodeToBase t)).radical) := by
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ht
  change IsStrictNormalCrossings ((specIdealSheaf (Base K (ι := ι))
      (Ideal.span {monomial K l})).comap
      (Spec.map (CommRingCat.ofHom (algebraMap (Base K (ι := ι)) (Chart K i))))).radical
  rw [specIdealSheaf_comap, Ideal.map_span, Set.image_singleton]
  exact chartBoundary_isStrictNormalCrossings K l i hi

/-- A genuine actual SNC divisor on the actual whole finite global coordinate-node tower. -/
theorem boundary_isStrictNormalCrossings (l : List ι) :
    IsStrictNormalCrossings (boundary K l) := by
  by_cases hnil : l = []
  · subst l
    have hb : baseRawBoundary K ([] : List ι) = ⊤ := by
      change (specIdealSheafEquiv (Base K (ι := ι))).symm (Ideal.span {(1 : Base K (ι := ι))}) = ⊤
      simp
    rw [boundary, rawBoundary, originalRawBoundary, hb,
      Scheme.IdealSheafData.comap_top, Scheme.IdealSheafData.comap_top,
      Scheme.IdealSheafData.radical_top]
    exact isStrictNormalCrossings_top _
  · have hz : (0 : Base K (ι := ι)) ∉ factors K l := by
      intro h
      obtain ⟨i, _, hi⟩ := List.mem_map.mp h
      exact X_ne_zero i hi
    have hne : factors K l ≠ [] := by simpa [factors] using hnil
    obtain ⟨S⟩ := nonempty_finishedCover (factors K l) hz hne
    apply SNCLocality.isStrictNormalCrossings_of_openCover (boundary K l) S.openCover
    intro i
    change S.I at i
    have hcoef : (S.inclusion i ≫ resolutionMorphism (factors K l)) ≫
        nodeToBase (factors K l).prod = nodeToBase (S.factor i) :=
      (Category.assoc _ _ _).trans (S.toBase i)
    change IsStrictNormalCrossings ((rawBoundary K l).radical.comap (S.inclusion i))
    rw [radical_comap_open, rawBoundary, originalRawBoundary,
      ← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp, hcoef]
    exact coefficientBoundary_isStrictNormalCrossings K l (S.factor i) (S.factor_mem i)

/-- The native finite coordinate-node producer with its actual reduced SNC total inverse image. -/
theorem regular_projective_alteration_snc (l : List ι) :
    IsRegularScheme (resolved (factors K l)) ∧
      IsProjectiveOver (resolutionMorphism (factors K l)) ∧
      IsAlteration (resolutionMorphism (factors K l)) ∧
      IsStrictNormalCrossings (boundary K l) := by
  obtain ⟨hreg, hproj, halt⟩ :=
    MonomialBlowupTowerRegular.polynomial_regular_projective_alteration K l
  exact ⟨hreg, hproj, halt, boundary_isStrictNormalCrossings K l⟩

end Hironaka.Geometry.MonomialBlowupTowerBoundary
