import Hironaka.Geometry.MonomialBlowupRegularBaseSNCNodeFactors
import Mathlib.Data.Finset.Sum

/-! Genuine prime factors and actual components of a several-component node boundary. -/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace Hironaka.Geometry.MonomialBlowupRegularBaseSNCNodeFamily

open Algebra.NodeBlowupChart Algebra.NodeNormalCoordinates
open MonomialBlowupRegularBaseSNCNodeAlgebra MonomialBlowupRegularBaseSNCParameters
open MonomialBlowupRegularBaseSNCNodeFactors
open SpecIdealSheaf ReducedClosedSubscheme Scheme.IdealSheafData

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable {A : Type u} [CommRing A]

/-- The literal two node coordinates and the original remaining coefficient equations. -/
def factor {ι : Type*} (t : A) (a : ι → A) : Fin 2 ⊕ ι → Node A t :=
  Sum.elim (coordinate t) (fun i ↦ algebraMap A (Node A t) (a i))

/-- The literal scheme-theoretic intersection of selected original boundary factors. -/
def factorIdeal {ι : Type*} (t : A) (a : ι → A) (s : Finset (Fin 2 ⊕ ι)) : Ideal (Node A t) :=
  Ideal.span (factor t a '' (s : Set (Fin 2 ⊕ ι)))

/-- The actual product boundary in the original node spectrum. -/
def boundary {ι : Type*} [Fintype ι] (t : A) (a : ι → A) :
    (Spec (CommRingCat.of (Node A t))).IdealSheafData :=
  specIdealSheaf (Node A t) (Ideal.span {∏ i, factor t a i})

/-- The native closed support of the original selected-factor ideal. -/
def factorClosed {ι : Type*} (t : A) (a : ι → A) (s : Finset (Fin 2 ⊕ ι)) :
    Closeds (Spec (CommRingCat.of (Node A t))) :=
  (specIdealSheaf (Node A t) (factorIdeal t a s)).support

/-- The literal original base boundary pulls back to the full product boundary, including scheme structure. -/
theorem boundary_eq_original_comap {ι : Type*} [Fintype ι] (t : A) (a : ι → A) :
    boundary t a = (specIdealSheaf A (Ideal.span {t * ∏ i, a i})).comap
      (Spec.map (CommRingCat.ofHom (algebraMap A (Node A t)))) := by
  have hp : (∏ i : Fin 2 ⊕ ι, factor t a i) =
      algebraMap A (Node A t) (t * ∏ i, a i) := by
    rw [Fintype.prod_sum_type]
    change (∏ i : Fin 2, coordinate t i) * (∏ i, algebraMap A (Node A t) (a i)) = _
    rw [Fin.prod_univ_two]
    have hnode : coordinate t 0 * coordinate t 1 = algebraMap A (Node A t) t :=
      Algebra.NodeDomain.nodeCoordinateProduct t
    rw [hnode, map_mul, map_prod]
  rw [specIdealSheaf_comap, Ideal.map_span, Set.image_singleton, boundary, hp]

/-- Prime membership gives the exact finite union of the original factor supports. -/
theorem boundary_support {ι : Type*} [Fintype ι] (t : A) (a : ι → A) :
    ((boundary t a).support : Set (Spec (CommRingCat.of (Node A t)))) =
      ⋃ i, (factorClosed t a {i} : Set (Spec (CommRingCat.of (Node A t)))) := by
  ext p
  let : p.asIdeal.IsPrime := p.isPrime
  simp only [boundary, factorClosed, specIdealSheaf_support, factorIdeal,
    Finset.coe_singleton, Set.image_singleton, PrimeSpectrum.zeroLocus_span,
    Set.mem_iUnion]
  change ({∏ i, factor t a i} : Set (Node A t)) ⊆ p.asIdeal ↔
    ∃ i, ({factor t a i} : Set (Node A t)) ⊆ p.asIdeal
  simp only [Set.singleton_subset_iff, SetLike.mem_coe]
  simpa only [Finset.mem_univ, true_and] using
    Ideal.IsPrime.prod_mem_iff (p := p.asIdeal) (s := Finset.univ) (x := factor t a)

variable [IsRegularRing A] [IsDomain A]

/-- All literal factors are prime, derived from the original SNC components. -/
theorem factor_prime
    (D : (Spec (CommRingCat.of A)).IdealSheafData) (hD : IsStrictNormalCrossings D)
    (F : Finset (DivisorComponent D)) (C : DivisorComponent D) (hC : C ∉ F)
    (t : A) (ht : specIdealSheaf A (Ideal.span {t}) = vanishingIdeal C.val)
    (a : F → A) (ha : ∀ B, specIdealSheaf A (Ideal.span {a B}) = vanishingIdeal B.val.val)
    (i : Fin 2 ⊕ F) : Prime (factor t a i) := by
  cases i with
  | inl i =>
    obtain ⟨hp, _, hreg⟩ := component_equation_data D hD C t ht
    let := hp
    let := hreg
    let : Fact (t ≠ 0) := ⟨component_equation_ne_zero D hD C t ht⟩
    exact MonomialBlowupRegularBaseSNCNodeBoundary.coordinate_prime i
  | inr B =>
    exact coefficient_prime D hD C B.val (by intro h; exact hC (h ▸ B.property)) t (a B) ht (ha B)

/-- Distinct actual component indices give nondividing original factors in the node. -/
theorem factor_not_dvd
    (D : (Spec (CommRingCat.of A)).IdealSheafData) (hD : IsStrictNormalCrossings D)
    (F : Finset (DivisorComponent D)) (C : DivisorComponent D) (hC : C ∉ F)
    (t : A) (ht : specIdealSheaf A (Ideal.span {t}) = vanishingIdeal C.val)
    (a : F → A) (ha : ∀ B, specIdealSheaf A (Ideal.span {a B}) = vanishingIdeal B.val.val)
    (i j : Fin 2 ⊕ F) (hij : i ≠ j) : ¬ factor t a i ∣ factor t a j := by
  let : IsDomain (Node A t) := Algebra.NodeDomain.nodeQuotient_isDomain t
    (component_equation_ne_zero D hD C t ht)
  let : (Ideal.span {t}).IsPrime := (component_equation_data D hD C t ht).1
  cases i with
  | inl i =>
    cases j with
    | inl j =>
      intro hdiv
      have hne : j ∉ ({i} : Finset (Fin 2)) := by
        simpa only [Finset.mem_singleton] using
          (show i ≠ j from fun h ↦ hij (congrArg (Sum.inl : Fin 2 → Fin 2 ⊕ F) h)).symm
      change coordinate t i ∣ coordinate t j at hdiv
      exact coordinate_not_mem_nodeIdeal t (component_equation_ne_zero D hD C t ht) {i} hne
        (by simpa only [nodeIdeal_singleton, Ideal.mem_span_singleton] using hdiv)
    | inr B =>
      exact coordinate_not_dvd_coefficient D hD C B.val
        (by intro h; exact hC (h ▸ B.property)) t (a B) ht (ha B) i
  | inr B =>
    cases j with
    | inl j =>
      intro hdiv
      have hassoc := (factor_prime D hD F C hC t ht a ha (.inr B)).associated_of_dvd
        (factor_prime D hD F C hC t ht a ha (.inl j)) hdiv
      exact coordinate_not_dvd_coefficient D hD C B.val
        (by intro h; exact hC (h ▸ B.property)) t (a B) ht (ha B) j hassoc.symm.dvd
    | inr B' =>
      exact coefficient_not_dvd_coefficient D hD C B.val B'.val
        (by intro h; exact hC (h ▸ B.property))
        (by intro h; apply hij; exact congrArg Sum.inr (Subtype.ext h))
        t (a B) (a B') ht (ha B) (ha B')

/-- The literal full product ideal is radical, without any UFD hypothesis. -/
theorem boundary_product_isRadical
    (D : (Spec (CommRingCat.of A)).IdealSheafData) (hD : IsStrictNormalCrossings D)
    (F : Finset (DivisorComponent D)) (C : DivisorComponent D) (hC : C ∉ F)
    (t : A) (ht : specIdealSheaf A (Ideal.span {t}) = vanishingIdeal C.val)
    (a : F → A) (ha : ∀ B, specIdealSheaf A (Ideal.span {a B}) = vanishingIdeal B.val.val) :
    (Ideal.span {∏ i, factor t a i}).IsRadical := by
  intro x hx
  obtain ⟨n, hn⟩ := hx
  apply Ideal.mem_span_singleton.mpr
  apply SNCSubdivisorProducts.prod_dvd_of_prime Finset.univ (factor t a)
  · intro i _
    exact factor_prime D hD F C hC t ht a ha i
  · intro i _ j _ hij
    exact factor_not_dvd D hD F C hC t ht a ha i j hij
  · intro i _
    exact (factor_prime D hD F C hC t ht a ha i).dvd_of_dvd_pow
      ((Finset.dvd_prod_of_mem (factor t a) (Finset.mem_univ i)).trans (Ideal.mem_span_singleton.mp hn))

/-- The actual product boundary subscheme is reduced. -/
theorem boundary_isReduced
    (D : (Spec (CommRingCat.of A)).IdealSheafData) (hD : IsStrictNormalCrossings D)
    (F : Finset (DivisorComponent D)) (C : DivisorComponent D) (hC : C ∉ F)
    (t : A) (ht : specIdealSheaf A (Ideal.span {t}) = vanishingIdeal C.val)
    (a : F → A) (ha : ∀ B, specIdealSheaf A (Ideal.span {a B}) = vanishingIdeal B.val.val) :
    IsReduced (boundary t a).subscheme := by
  have hr : (boundary t a).radical = boundary t a := by
    rw [boundary, specIdealSheaf_radical, (boundary_product_isRadical D hD F C hC t ht a ha).radical]
  simpa only [hr] using isReduced_radical_subscheme (boundary t a)

section Components

variable (D : (Spec (CommRingCat.of A)).IdealSheafData) (hD : IsStrictNormalCrossings D)
variable (F : Finset (DivisorComponent D)) (C : DivisorComponent D) (hC : C ∉ F)
variable (t : A) (ht : specIdealSheaf A (Ideal.span {t}) = vanishingIdeal C.val)
variable (a : F → A) (ha : ∀ B, specIdealSheaf A (Ideal.span {a B}) = vanishingIdeal B.val.val)

include hD hC ht ha

/-- Every original factor ideal is the actual prime ideal generated by its literal equation. -/
theorem factorIdeal_singleton_isPrime (i : Fin 2 ⊕ F) : (factorIdeal t a {i}).IsPrime := by
  have hp := factor_prime D hD F C hC t ht a ha i
  have hI : factorIdeal t a {i} = Ideal.span {factor t a i} := by simp [factorIdeal]
  rw [hI]
  exact (Ideal.span_singleton_prime hp.ne_zero).mpr hp

/-- Every original factor support is genuinely irreducible. -/
theorem factorClosed_singleton_isIrreducible (i : Fin 2 ⊕ F) :
    IsIrreducible (factorClosed t a {i} : Set (Spec (CommRingCat.of (Node A t)))) := by
  let := factorIdeal_singleton_isPrime D hD F C hC t ht a ha i
  rw [factorClosed, specIdealSheaf_support]
  exact (PrimeSpectrum.isIrreducible_zeroLocus_iff_of_radical _ ‹(factorIdeal t a {i}).IsPrime›.isRadical).mpr
    inferInstance

/-- Every actual irreducible boundary component is an original factor support. -/
theorem component_eq_factorClosed (B : DivisorComponent (boundary t a)) :
    ∃ i : Fin 2 ⊕ F, B.val = factorClosed t a {i} := by
  classical
  let X := Spec (CommRingCat.of (Node A t))
  let E := boundary t a
  obtain ⟨S, hS, hB⟩ := B.property
  have hirred : IsIrreducible (B.val : Set X) := by
    rw [← hB]
    exact hS.1.image Subtype.val continuous_subtype_val.continuousOn
  let G := (Finset.univ : Finset (Fin 2 ⊕ F)).image (fun i ↦ (factorClosed t a {i} : Set X))
  have hcover : (B.val : Set X) ⊆ ⋃₀ (G : Set (Set X)) := by
    intro x hx
    have hxE := SNCSubdivisorComponent.component_le_support E B hx
    change x ∈ ((boundary t a).support : Set X) at hxE
    rw [boundary_support] at hxE
    obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hxE
    exact Set.mem_sUnion.mpr ⟨_, Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩, hxi⟩
  obtain ⟨Z, hZ, hBZ⟩ := isIrreducible_iff_sUnion_isClosed.mp hirred G
    (by intro Z hZ; obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hZ;
        exact (factorClosed t a {i}).isClosed) hcover
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hZ
  have hfactorE : (factorClosed t a {i} : Set X) ⊆ E.support := by
    rw [boundary_support]
    intro x hx
    exact Set.mem_iUnion.mpr ⟨i, hx⟩
  have hZB := SNCSubdivisorTopology.component_maximal E B _
    (factorClosed_singleton_isIrreducible D hD F C hC t ht a ha i) hBZ hfactorE
  exact ⟨i, Closeds.ext (Set.Subset.antisymm hBZ hZB)⟩

/-- The internally determined original-factor index of an actual irreducible boundary component. -/
def componentIndex (B : DivisorComponent (boundary t a)) : Fin 2 ⊕ F :=
  (component_eq_factorClosed D hD F C hC t ht a ha B).choose

/-- The actual component equals its original selected factor support. -/
theorem componentIndex_closed (B : DivisorComponent (boundary t a)) :
    B.val = factorClosed t a {componentIndex D hD F C hC t ht a ha B} :=
  (component_eq_factorClosed D hD F C hC t ht a ha B).choose_spec

/-- Distinct actual components retain distinct original-factor indices. -/
theorem componentIndex_injective : Function.Injective (componentIndex D hD F C hC t ht a ha) := by
  intro B B' h
  apply Subtype.ext
  rw [componentIndex_closed D hD F C hC t ht a ha B,
    componentIndex_closed D hD F C hC t ht a ha B', h]

/-- The reduced ideal of an actual original factor support is its full original principal ideal. -/
theorem vanishingIdeal_factorClosed_singleton (i : Fin 2 ⊕ F) :
    vanishingIdeal (factorClosed t a {i}) = specIdealSheaf (Node A t) (factorIdeal t a {i}) := by
  let := factorIdeal_singleton_isPrime D hD F C hC t ht a ha i
  apply idealSheaf_eq_of_radical_of_support_eq
  · exact radical_vanishingIdeal _
  · rw [specIdealSheaf_radical, ‹(factorIdeal t a {i}).IsPrime›.isRadical.radical]
  · rfl

/-- Containment of original factor supports forces equality of the original factor indices. -/
theorem eq_of_factorClosed_subset (i j : Fin 2 ⊕ F)
    (hij : (factorClosed t a {i} : Set (Spec (CommRingCat.of (Node A t)))) ⊆ factorClosed t a {j}) :
    i = j := by
  let := factorIdeal_singleton_isPrime D hD F C hC t ht a ha i
  let p : PrimeSpectrum (Node A t) := ⟨factorIdeal t a {i}, inferInstance⟩
  have hpi : p ∈ (factorClosed t a {i} : Set (Spec (CommRingCat.of (Node A t)))) := by
    rw [factorClosed, specIdealSheaf_support]
    exact (show factorIdeal t a {i} ≤ factorIdeal t a {i} from le_rfl)
  have hpj := hij hpi
  rw [factorClosed, specIdealSheaf_support] at hpj
  have hmem : factor t a j ∈ factorIdeal t a {i} := hpj
    (Ideal.subset_span (Set.mem_image_of_mem _ (Finset.mem_singleton_self j)))
  have hdiv : factor t a i ∣ factor t a j := by
    apply Ideal.mem_span_singleton.mp
    simpa only [factorIdeal, Finset.coe_singleton, Set.image_singleton] using hmem
  by_contra hne
  exact factor_not_dvd D hD F C hC t ht a ha i j hne hdiv

/-- Every original factor support is an actual irreducible component of the literal boundary. -/
theorem exists_component_eq_factorClosed (i : Fin 2 ⊕ F) :
    ∃ B : DivisorComponent (boundary t a), B.val = factorClosed t a {i} := by
  have hfactorE : (factorClosed t a {i} : Set (Spec (CommRingCat.of (Node A t)))) ⊆
      (boundary t a).support := by
    rw [boundary_support]
    intro x hx
    exact Set.mem_iUnion.mpr ⟨i, hx⟩
  obtain ⟨B, hB⟩ := BoundaryEnlargement.exists_component_containing (boundary t a) _
    (factorClosed_singleton_isIrreducible D hD F C hC t ht a ha i) hfactorE
  obtain ⟨j, hj⟩ := component_eq_factorClosed D hD F C hC t ht a ha B
  have heq : i = j := eq_of_factorClosed_subset D hD F C hC t ht a ha i j (by rwa [← hj])
  exact ⟨B, by rw [hj, ← heq]⟩

end Components

end Hironaka.Geometry.MonomialBlowupRegularBaseSNCNodeFamily
