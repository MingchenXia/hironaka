import Hironaka.Geometry.MonomialBlowupRegularBaseSNCNodeNativeSNC
import Hironaka.Geometry.MonomialBlowupRegularBaseSNC

/-! Genuine regular projective monomial tower alteration with the full original reduced SNC boundary. -/

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace Hironaka.Geometry.MonomialBlowupRegularBaseSNCTower

open SpecIdealSheaf ReducedClosedSubscheme Scheme.IdealSheafData
open MonomialBlowupRegularBaseSNCParameters MonomialBlowupRegularBaseSNCNodeNativeSNC
open MonomialBlowupTower MonomialBlowupTowerBoundaryCover
open MonomialBlowupTowerBoundaryPolynomial

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable {A : Type u} [CommRing A]

local instance componentDecidableEq (D : (Spec (CommRingCat.of A)).IdealSheafData) :
    DecidableEq (DivisorComponent D) := Classical.typeDecidableEq _

/-- Original equations of the same actual component have identical membership in every actual ideal. -/
theorem mem_iff_of_same_component
    (D : (Spec (CommRingCat.of A)).IdealSheafData) (C : DivisorComponent D)
    (a b : A) (ha : specIdealSheaf A (Ideal.span {a}) = vanishingIdeal C.val)
    (hb : specIdealSheaf A (Ideal.span {b}) = vanishingIdeal C.val) (P : Ideal A) : a ∈ P ↔ b ∈ P := by
  have hI : Ideal.span {a} = Ideal.span {b} :=
    (specIdealSheafEquiv A).symm.injective (ha.trans hb.symm)
  constructor
  · intro hamem
    have hle : Ideal.span {a} ≤ P := Ideal.span_le.mpr (by simpa using hamem)
    rw [hI] at hle
    exact hle (Ideal.subset_span (Set.mem_singleton _))
  · intro hbmem
    have hle : Ideal.span {b} ≤ P := Ideal.span_le.mpr (by simpa using hbmem)
    rw [← hI] at hle
    exact hle (Ideal.subset_span (Set.mem_singleton _))

/-- Prime membership of the original finite list product remembers precisely its original factors. -/
theorem list_prod_mem_iff (P : Ideal A) [P.IsPrime] (l : List A) :
    l.prod ∈ P ↔ ∃ a ∈ l, a ∈ P := by
  simpa using (inferInstance : P.IsPrime).multiset_prod_mem_iff_exists_mem (l : Multiset A)

/-- Actual distinct components and their equations are selected internally from the original list. -/
theorem exists_component_product
    (D : (Spec (CommRingCat.of A)).IdealSheafData) (l : List A)
    (hfactors : ∀ a ∈ l, ∃ C : DivisorComponent D,
      specIdealSheaf A (Ideal.span {a}) = vanishingIdeal C.val)
    (s : A) (hs : s ∈ l) :
    ∃ C : DivisorComponent D, ∃ F : Finset (DivisorComponent D), C ∉ F ∧ ∃ a : F → A,
      specIdealSheaf A (Ideal.span {s}) = vanishingIdeal C.val ∧
      (∀ B, specIdealSheaf A (Ideal.span {a B}) = vanishingIdeal B.val.val) ∧
      ∀ (P : Ideal A) [P.IsPrime], l.prod ∈ P ↔ s * ∏ B, a B ∈ P := by
  classical
  let T := l.toFinset
  let cmp : T → DivisorComponent D := fun r ↦ (hfactors r.val (List.mem_toFinset.mp r.property)).choose
  have hcmp (r : T) : specIdealSheaf A (Ideal.span {r.val}) = vanishingIdeal (cmp r).val :=
    (hfactors r.val (List.mem_toFinset.mp r.property)).choose_spec
  let si : T := ⟨s, List.mem_toFinset.mpr hs⟩
  let C := cmp si
  let all := Finset.univ.image cmp
  let F := all.erase C
  have hC : C ∉ F := by simp [F]
  have hwitness (B : F) : ∃ r : T, r ∈ Finset.univ ∧ cmp r = B.val :=
    Finset.mem_image.mp (Finset.mem_of_mem_erase B.property)
  let repr : F → T := fun B ↦ (hwitness B).choose
  have hrepr (B : F) : cmp (repr B) = B.val := (hwitness B).choose_spec.2
  let a : F → A := fun B ↦ (repr B).val
  have ha (B : F) : specIdealSheaf A (Ideal.span {a B}) = vanishingIdeal B.val.val := by
    have h := hcmp (repr B)
    rw [hrepr] at h
    exact h
  refine ⟨C, F, hC, a, hcmp si, ha, ?_⟩
  intro P hP
  rw [list_prod_mem_iff]
  constructor
  · rintro ⟨r, hrl, hrP⟩
    let ri : T := ⟨r, List.mem_toFinset.mpr hrl⟩
    by_cases heq : cmp ri = C
    · have hr : specIdealSheaf A (Ideal.span {r}) = vanishingIdeal C.val := by
        have h := hcmp ri
        rwa [heq] at h
      have hsP : s ∈ P := (mem_iff_of_same_component D C r s hr (hcmp si) P).mp hrP
      exact P.mul_mem_right _ hsP
    · have hmem : cmp ri ∈ F := Finset.mem_erase.mpr
        ⟨heq, Finset.mem_image_of_mem cmp (Finset.mem_univ ri)⟩
      let B : F := ⟨cmp ri, hmem⟩
      have haP : a B ∈ P :=
        (mem_iff_of_same_component D (cmp ri) r (a B) (hcmp ri) (ha B) P).mp hrP
      have hprod : (∏ B, a B) ∈ P := Ideal.IsPrime.prod_mem_iff.mpr ⟨B, Finset.mem_univ B, haP⟩
      exact P.mul_mem_left s hprod
  · intro hprod
    rcases (inferInstance : P.IsPrime).mem_or_mem hprod with hsP | haP
    · exact ⟨s, hs, hsP⟩
    · obtain ⟨B, _, hBP⟩ := Ideal.IsPrime.prod_mem_iff.mp haP
      exact ⟨a B, List.mem_toFinset.mp (repr B).property, hBP⟩

variable [IsRegularRing A] [IsDomain A]

/-- Arbitrary original multiplicities and unit multiples reduce to the genuine several-component node boundary. -/
theorem coefficientBoundary_radical_isStrictNormalCrossings
    (D : (Spec (CommRingCat.of A)).IdealSheafData) (hD : IsStrictNormalCrossings D)
    (l : List A) (hfactors : ∀ a ∈ l, ∃ C : DivisorComponent D,
      specIdealSheaf A (Ideal.span {a}) = vanishingIdeal C.val)
    (s : A) (hs : s ∈ l) : IsStrictNormalCrossings
      (((MonomialBlowupRegularBaseSNC.baseRawBoundary l).comap (nodeToBase s)).radical) := by
  obtain ⟨C, F, hC, a, hsC, ha, hprimes⟩ := exists_component_product D l hfactors s hs
  let E := (specIdealSheaf A (Ideal.span {s * ∏ B, a B})).comap (nodeToBase s)
  have hE : IsStrictNormalCrossings E := original_comap_isStrictNormalCrossings D hD F C hC s hsC a ha
  have hsupp : (MonomialBlowupRegularBaseSNC.baseRawBoundary l).support =
      (specIdealSheaf A (Ideal.span {s * ∏ B, a B})).support := by
    apply TopologicalSpace.Closeds.ext
    rw [MonomialBlowupRegularBaseSNC.baseRawBoundary, specIdealSheaf_support, specIdealSheaf_support]
    ext p
    let : p.asIdeal.IsPrime := p.isPrime
    change Ideal.span {l.prod} ≤ p.asIdeal ↔ Ideal.span {s * ∏ B, a B} ≤ p.asIdeal
    have h := hprimes p.asIdeal
    simpa only [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe] using h
  have heq : ((MonomialBlowupRegularBaseSNC.baseRawBoundary l).comap (nodeToBase s)).radical = E := by
    apply idealSheaf_eq_of_radical_of_support_eq
    · let : IsReduced (((MonomialBlowupRegularBaseSNC.baseRawBoundary l).comap (nodeToBase s)).radical).subscheme :=
        isReduced_radical_subscheme _
      exact idealSheaf_radical_eq_of_isReduced _
    · let : IsReduced E.subscheme := hE.reduced
      exact idealSheaf_radical_eq_of_isReduced E
    · rw [support_radical, support_comap, hsupp, support_comap]
  rw [heq]
  exact hE

/-- The original whole finite global tower has its actual reduced SNC total inverse-image boundary. -/
theorem boundary_isStrictNormalCrossings
    (D : (Spec (CommRingCat.of A)).IdealSheafData) (hD : IsStrictNormalCrossings D)
    (l : List A) (hfactors : ∀ a ∈ l, ∃ C : DivisorComponent D,
      specIdealSheaf A (Ideal.span {a}) = vanishingIdeal C.val) :
    IsStrictNormalCrossings (MonomialBlowupRegularBaseSNC.boundary l) := by
  by_cases hnil : l = []
  · subst l
    have hb : MonomialBlowupRegularBaseSNC.baseRawBoundary ([] : List A) = ⊤ := by
      change (specIdealSheafEquiv A).symm (Ideal.span {(1 : A)}) = ⊤
      simp
    rw [MonomialBlowupRegularBaseSNC.boundary, MonomialBlowupRegularBaseSNC.rawBoundary,
      MonomialBlowupRegularBaseSNC.originalRawBoundary, hb,
      Scheme.IdealSheafData.comap_top, Scheme.IdealSheafData.comap_top,
      Scheme.IdealSheafData.radical_top]
    exact isStrictNormalCrossings_top _
  · have hz : (0 : A) ∉ l := by
      intro h
      obtain ⟨C, hC⟩ := hfactors 0 h
      exact component_equation_ne_zero D hD C 0 hC rfl
    obtain ⟨S⟩ := nonempty_finishedCover l hz hnil
    apply SNCLocality.isStrictNormalCrossings_of_openCover (MonomialBlowupRegularBaseSNC.boundary l) S.openCover
    intro i
    change S.I at i
    have hcoef : (S.inclusion i ≫ resolutionMorphism l) ≫ nodeToBase l.prod = nodeToBase (S.factor i) :=
      (Category.assoc _ _ _).trans (S.toBase i)
    change IsStrictNormalCrossings ((MonomialBlowupRegularBaseSNC.rawBoundary l).radical.comap (S.inclusion i))
    rw [radical_comap_open, MonomialBlowupRegularBaseSNC.rawBoundary,
      MonomialBlowupRegularBaseSNC.originalRawBoundary,
      ← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp, hcoef]
    exact coefficientBoundary_radical_isStrictNormalCrossings D hD l hfactors (S.factor i) (S.factor_mem i)

/-- The actual full regular-base monomial tower with its original reduced total boundary. -/
theorem regular_projective_alteration_snc
    (D : (Spec (CommRingCat.of A)).IdealSheafData) (hD : IsStrictNormalCrossings D)
    (l : List A) (hfactors : ∀ a ∈ l, ∃ C : DivisorComponent D,
      specIdealSheaf A (Ideal.span {a}) = vanishingIdeal C.val) :
    IsRegularScheme (resolved l) ∧ IsProjectiveOver (resolutionMorphism l) ∧
      IsAlteration (resolutionMorphism l) ∧
      IsStrictNormalCrossings (MonomialBlowupRegularBaseSNC.boundary l) := by
  obtain ⟨hreg, hproj, halt⟩ := regular_projective_alteration_of_snc_components D hD l hfactors
  exact ⟨hreg, hproj, halt, boundary_isStrictNormalCrossings D hD l hfactors⟩

end Hironaka.Geometry.MonomialBlowupRegularBaseSNCTower
