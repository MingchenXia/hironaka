import Hironaka.Geometry.MonomialBlowupRegularBaseSNCNodeBoundary
import Hironaka.Geometry.MonomialBlowupTowerBoundaryCover
import Hironaka.Geometry.SNCLocality
import Hironaka.Geometry.MonomialBlowupTowerBoundaryPolynomial

/-!
# Actual reduced SNC total boundary for factors of one genuine component

Every original factor cuts out the same actual base component; the factors may
have different unit multiples. Their full product and the native tower are retained.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace Hironaka.Geometry.MonomialBlowupRegularBaseSNC

open SpecIdealSheaf ReducedClosedSubscheme Scheme.IdealSheafData
open MonomialBlowupTower MonomialBlowupTowerBoundaryCover MonomialBlowupTowerBoundaryPolynomial
open MonomialBlowupRegularBaseSNCParameters MonomialBlowupRegularBaseSNCNodeBoundary

universe u
variable {A : Type u} [CommRing A]

/-- The original coefficient ideal with its full original multiplicity. -/
def baseRawBoundary (l : List A) : (Spec (CommRingCat.of A)).IdealSheafData :=
  specIdealSheaf A (Ideal.span {l.prod})

/-- The original coefficient pullback to the actual finite-product node. -/
def originalRawBoundary (l : List A) : (original l).IdealSheafData :=
  (baseRawBoundary l).comap (nodeToBase l.prod)

/-- The literal total inverse image under the actual finite original-prefix tower. -/
def rawBoundary (l : List A) : (resolved l).IdealSheafData :=
  (originalRawBoundary l).comap (resolutionMorphism l)

/-- The actual reduced total inverse-image ideal on the actual whole tower. -/
def boundary (l : List A) : (resolved l).IdealSheafData := (rawBoundary l).radical

/-- The original support is retained under genuine total inverse image and reduction. -/
theorem boundary_support (l : List A) : (boundary l).support =
    (originalRawBoundary l).support.preimage (resolutionMorphism l).continuous := by
  rw [boundary, support_radical, rawBoundary, support_comap]

/-- The original factor product retains its exact ideal multiplicity, including arbitrary unit multiples. -/
theorem span_prod_eq_pow (l : List A) (s : A)
    (h : ∀ t ∈ l, Ideal.span {t} = Ideal.span {s}) :
    Ideal.span {l.prod} = (Ideal.span {s}) ^ l.length := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.prod_cons, ← Ideal.span_singleton_mul_span_singleton,
      h a List.mem_cons_self, ih (fun t ht ↦ h t (List.mem_cons_of_mem a ht)),
      List.length_cons, pow_succ']

variable [IsRegularRing A] [IsDomain A]

omit [IsRegularRing A] [IsDomain A] in
/-- A finite list of equations of the same actual component has the exact power of every chosen equation ideal. -/
theorem component_product_ideal
    (D : (Spec (CommRingCat.of A)).IdealSheafData) (C : DivisorComponent D)
    (l : List A)
    (hfactors : ∀ t ∈ l, specIdealSheaf A (Ideal.span {t}) = vanishingIdeal C.val)
    (s : A) (hs : s ∈ l) : Ideal.span {l.prod} = (Ideal.span {s}) ^ l.length := by
  apply span_prod_eq_pow
  intro t ht
  apply (specIdealSheafEquiv A).symm.injective
  exact (hfactors t ht).trans (hfactors s hs).symm

/-- On each genuine finished node, the positive original multiplicity reduces to the literal two-axis ideal. -/
theorem coefficientBoundary_radical
    (D : (Spec (CommRingCat.of A)).IdealSheafData) (hD : IsStrictNormalCrossings D)
    (C : DivisorComponent D) (l : List A)
    (hfactors : ∀ t ∈ l, specIdealSheaf A (Ideal.span {t}) = vanishingIdeal C.val)
    (s : A) (hs : s ∈ l) :
    ((baseRawBoundary l).comap (nodeToBase s)).radical = coefficientDivisor s := by
  let := coefficientDivisor_isReduced D hD C s (hfactors s hs)
  have hn : l.length ≠ 0 := List.length_pos_iff.mpr (List.ne_nil_of_mem hs) |>.ne'
  rw [baseRawBoundary, component_product_ideal D C l hfactors s hs, nodeToBase,
    specIdealSheaf_comap, Ideal.map_pow, Ideal.map_span, Set.image_singleton,
    specIdealSheaf_radical]
  rw [Ideal.radical_pow (I := Ideal.span {algebraMap A (Algebra.NodeBlowupChart.Node A s) s}) hn]
  rw [← specIdealSheaf_radical]
  change (coefficientDivisor s).radical = coefficientDivisor s
  exact idealSheaf_radical_eq_of_isReduced _

/-- Actual SNC descent for a nonempty list of equations of one genuine base component. -/
theorem boundary_isStrictNormalCrossings
    (D : (Spec (CommRingCat.of A)).IdealSheafData) (hD : IsStrictNormalCrossings D)
    (C : DivisorComponent D) (l : List A) (hne : l ≠ [])
    (hfactors : ∀ t ∈ l, specIdealSheaf A (Ideal.span {t}) = vanishingIdeal C.val) :
    IsStrictNormalCrossings (boundary l) := by
  have hz : (0 : A) ∉ l := by
    intro h
    exact component_equation_ne_zero D hD C 0 (hfactors 0 h) rfl
  obtain ⟨S⟩ := nonempty_finishedCover l hz hne
  apply SNCLocality.isStrictNormalCrossings_of_openCover (boundary l) S.openCover
  intro i
  change S.I at i
  have hcoef : (S.inclusion i ≫ resolutionMorphism l) ≫
      nodeToBase l.prod = nodeToBase (S.factor i) :=
    (Category.assoc _ _ _).trans (S.toBase i)
  change IsStrictNormalCrossings ((rawBoundary l).radical.comap (S.inclusion i))
  rw [radical_comap_open, rawBoundary, originalRawBoundary,
    ← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp, hcoef,
    coefficientBoundary_radical D hD C l hfactors (S.factor i) (S.factor_mem i)]
  exact coefficientDivisor_isStrictNormalCrossings D hD C _ (hfactors _ (S.factor_mem i))

/-- A native regular projective tower alteration with its actual reduced SNC total boundary,
from equations of a genuine component of an actual SNC base divisor, retaining arbitrary multiplicity. -/
theorem regular_projective_alteration_snc
    (D : (Spec (CommRingCat.of A)).IdealSheafData) (hD : IsStrictNormalCrossings D)
    (C : DivisorComponent D) (l : List A) (hne : l ≠ [])
    (hfactors : ∀ t ∈ l, specIdealSheaf A (Ideal.span {t}) = vanishingIdeal C.val) :
    IsRegularScheme (resolved l) ∧ IsProjectiveOver (resolutionMorphism l) ∧
      IsAlteration (resolutionMorphism l) ∧ IsStrictNormalCrossings (boundary l) := by
  obtain ⟨hreg, hproj, halt⟩ :=
    regular_projective_alteration_of_snc_components D hD l (by
      intro t ht
      exact ⟨C, hfactors t ht⟩)
  exact ⟨hreg, hproj, halt, boundary_isStrictNormalCrossings D hD C l hne hfactors⟩

end Hironaka.Geometry.MonomialBlowupRegularBaseSNC
