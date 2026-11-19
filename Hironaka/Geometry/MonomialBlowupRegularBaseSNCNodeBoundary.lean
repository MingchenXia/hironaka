import Hironaka.Geometry.MonomialBlowupRegularBaseSNCNodeAlgebra
import Hironaka.Geometry.MonomialBlowupRegularBaseSNCParameters
import Hironaka.Geometry.CoordinateSNC
import Hironaka.Geometry.SNCSubdivisorProducts

/-!
# Actual two-branch SNC boundary over a genuine regular-base component

The component classification argument follows CoordinateSNC, replacing free
coordinate ideals by the exact original node-coordinate ideals and quotient rings.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace IsLocalRing

namespace Hironaka.Geometry.MonomialBlowupRegularBaseSNCNodeBoundary

open Algebra.NodeBlowupChart Algebra.NodeNormalCoordinates
open MonomialBlowupRegularBaseSNCNodeAlgebra SpecIdealSheaf ReducedClosedSubscheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable {A : Type u} [CommRing A] [IsDomain A] [IsRegularRing A]
variable {t : A} [Fact (t ≠ 0)] [(Ideal.span {t}).IsPrime] [IsRegularRing (ParameterQuotient t)]

local instance : IsDomain (Node A t) := Algebra.NodeDomain.nodeQuotient_isDomain t (Fact.out : t ≠ 0)
local instance nodeIdealPrime (s : Finset (Fin 2)) : (nodeIdeal t s).IsPrime := nodeIdeal_isPrime t (Fact.out : t ≠ 0) s

omit [IsRegularRing A] [IsRegularRing (ParameterQuotient t)] in
/-- The original node coordinates are actual prime elements. -/
theorem coordinate_prime (i : Fin 2) : Prime (coordinate t i) := by
  have hp : (Ideal.span {coordinate t i}).IsPrime := by
    have h := nodeIdealPrime (t := t) {i}
    rw [nodeIdeal_singleton] at h
    exact h
  exact (Ideal.span_singleton_prime
    (Algebra.NodeDomain.nodeCoordinate_ne_zero t (Fact.out : t ≠ 0) i)).mp hp

omit [IsRegularRing A] [IsRegularRing (ParameterQuotient t)] in
/-- Distinct original node coordinates are relatively prime. -/
theorem coordinate_isRelPrime {i j : Fin 2} (hij : i ≠ j) :
    IsRelPrime (coordinate t i) (coordinate t j) := by
  apply (coordinate_prime (t := t) i).irreducible.isRelPrime_iff_not_dvd.mpr
  intro h
  apply coordinate_not_mem_nodeIdeal t (Fact.out : t ≠ 0) {i} (by simpa using hij.symm)
  simpa only [nodeIdeal_singleton, Ideal.mem_span_singleton] using h

omit [IsRegularRing A] [IsRegularRing (ParameterQuotient t)] in
/-- The original product boundary is genuinely radical. -/
theorem nodeProduct_isRadical (s : Finset (Fin 2)) :
    (Ideal.span {∏ i ∈ s, coordinate t i}).IsRadical := by
  intro x hx
  obtain ⟨n, hn⟩ := hx
  apply Ideal.mem_span_singleton.mpr
  apply SNCSubdivisorProducts.prod_dvd_of_prime s (coordinate t)
  · intro i _
    exact coordinate_prime (t := t) i
  · intro i _ j _ hij hdiv
    apply coordinate_not_mem_nodeIdeal t (Fact.out : t ≠ 0) {i} (by simpa using hij.symm)
    simpa only [nodeIdeal_singleton, Ideal.mem_span_singleton] using hdiv
  · intro i hi
    apply (coordinate_prime (t := t) i).dvd_of_dvd_pow
    exact (Finset.dvd_prod_of_mem (coordinate t) hi).trans (Ideal.mem_span_singleton.mp hn)

/-- The native closed coordinate intersection. -/
def nodeClosed (s : Finset (Fin 2)) : Closeds (Spec (CommRingCat.of (Node A t))) :=
  (specIdealSheaf (Node A t) (nodeIdeal t s)).support

omit [IsRegularRing A] [IsRegularRing (ParameterQuotient t)] in
theorem nodeClosed_isIrreducible (s : Finset (Fin 2)) :
    IsIrreducible (nodeClosed (t := t) s :
      Set (Spec (CommRingCat.of (Node A t)))) := by
  rw [nodeClosed, specIdealSheaf_support]
  exact (PrimeSpectrum.isIrreducible_zeroLocus_iff_of_radical _
    (nodeIdealPrime (t := t) s).isRadical).mpr inferInstance

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
omit [IsRegularRing (ParameterQuotient t)] in
/-- Pure codimension is computed in the actual ambient scheme stalks. -/
theorem nodeClosed_hasPureCodimension (s : Finset (Fin 2)) :
    HasPureCodimension (nodeClosed (t := t) s) s.card := by
  let T := nodeClosed (t := t) s
  let : IrreducibleSpace T := Subtype.irreducibleSpace (nodeClosed_isIrreducible s)
  intro C hC x hx
  have hCeq : C = Set.univ := by
    simpa only [irreducibleComponents_eq_singleton, Set.mem_singleton_iff] using hC
  let q : Spec (CommRingCat.of (Node A t)) :=
    (⟨nodeIdeal t s, inferInstance⟩ : PrimeSpectrum (Node A t))
  have hgeneric : IsGenericPoint q
      (T : Set (Spec (CommRingCat.of (Node A t)))) := by
    have h := PrimeSpectrum.closure_singleton
      (⟨nodeIdeal t s, inferInstance⟩ : PrimeSpectrum (Node A t))
    exact h.trans (specIdealSheaf_support _ _).symm
  have himage : (Subtype.val : T → Spec (CommRingCat.of (Node A t))) '' C =
      (T : Set (Spec (CommRingCat.of (Node A t)))) := by
    ext y
    simp [hCeq]
  have hxeq : x = q := by
    rw [himage] at hx
    exact hx.eq hgeneric
  rw [hxeq, ringKrullDim_stalk_eq_coheight, ← idealHeight_eq_coheight]
  exact_mod_cast nodeIdeal_height t (Fact.out : t ≠ 0) s

/-- The actual native divisor cut out by a product of distinct coordinates. -/
def nodeDivisor (s : Finset (Fin 2)) :
    (Spec (CommRingCat.of (Node A t))).IdealSheafData :=
  specIdealSheaf (Node A t) (Ideal.span {∏ i ∈ s, coordinate t i})

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
omit [IsDomain A] [IsRegularRing A] [Fact (t ≠ 0)] [(Ideal.span {t}).IsPrime]
  [IsRegularRing (ParameterQuotient t)] in
theorem nodeDivisor_support (s : Finset (Fin 2)) :
    ((nodeDivisor (t := t) s).support :
      Set (Spec (CommRingCat.of (Node A t)))) =
    ⋃ i ∈ s, (nodeClosed (t := t) {i} :
      Set (Spec (CommRingCat.of (Node A t)))) := by
  have hring : PrimeSpectrum.zeroLocus
      (Ideal.span {∏ i ∈ s, (coordinate t i : Node A t)} : Set (Node A t)) =
      ⋃ i ∈ s, PrimeSpectrum.zeroLocus (nodeIdeal t {i} : Set (Node A t)) := by
    ext p
    let : p.asIdeal.IsPrime := p.isPrime
    simp only [nodeIdeal, Finset.coe_singleton, Set.image_singleton,
      PrimeSpectrum.zeroLocus_span, PrimeSpectrum.mem_zeroLocus,
      Set.singleton_subset_iff, Set.mem_iUnion]
    constructor
    · intro h
      obtain ⟨i, hi, hXi⟩ := (Ideal.IsPrime.prod_mem_iff (p := p.asIdeal) (s := s)
        (x := fun i ↦ (coordinate t i : Node A t))).mp h
      exact ⟨i, hi, hXi⟩
    · rintro ⟨i, hi, hXi⟩
      exact (Ideal.IsPrime.prod_mem_iff (p := p.asIdeal) (s := s)
        (x := fun i ↦ (coordinate t i : Node A t))).mpr ⟨i, hi, hXi⟩
  simpa only [nodeDivisor, nodeClosed, specIdealSheaf_support] using hring

omit [IsRegularRing A] [IsRegularRing (ParameterQuotient t)] in
theorem nodeClosed_singleton_injective :
    Function.Injective (nodeClosed (t := t) ∘ (Singleton.singleton : Fin 2 → Finset (Fin 2))) := by
  intro i j hij
  change nodeClosed (t := t) {i} = nodeClosed {j} at hij
  by_contra hne
  let p : PrimeSpectrum (Node A t) := ⟨nodeIdeal t {i}, inferInstance⟩
  have hpi : p ∈ (nodeClosed (t := t) {i} :
      Set (Spec (CommRingCat.of (Node A t)))) := by
    rw [nodeClosed, specIdealSheaf_support]
    change nodeIdeal t {i} ≤ nodeIdeal t {i}
    exact le_rfl
  have hpj : p ∈ (nodeClosed (t := t) {j} :
      Set (Spec (CommRingCat.of (Node A t)))) := by
    rw [← hij]
    exact hpi
  rw [nodeClosed, specIdealSheaf_support] at hpj
  apply coordinate_not_mem_nodeIdeal t (Fact.out : t ≠ 0) {i} (by simpa using (Ne.symm hne))
  exact hpj (Ideal.subset_span (Set.mem_image_of_mem (coordinate t) (Finset.mem_singleton_self j)))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
omit [IsRegularRing A] [IsRegularRing (ParameterQuotient t)] in
/-- Actual components of the coordinate union are its coordinate hyperplanes. -/
theorem component_eq_nodeClosed (s : Finset (Fin 2))
    (C : DivisorComponent (nodeDivisor (t := t) s)) :
    ∃ i ∈ s, C.val = nodeClosed {i} := by
  classical
  let X := Spec (CommRingCat.of (Node A t))
  let D := nodeDivisor (t := t) s
  obtain ⟨S, hS, hC⟩ := C.property
  have hirred : IsIrreducible (C.val : Set X) := by
    rw [← hC]
    exact hS.1.image Subtype.val continuous_subtype_val.continuousOn
  have hcover : (C.val : Set X) ⊆
      ⋃₀ ↑(s.image (fun i ↦ (nodeClosed (t := t) {i} : Set X))) := by
    intro x hx
    obtain ⟨y, _, rfl⟩ := hC ▸ hx
    have hy : y.val ∈ ((nodeDivisor (t := t) s).support : Set X) := y.property
    rw [nodeDivisor_support] at hy
    obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hy
    obtain ⟨his, hxi⟩ := Set.mem_iUnion.mp hxi
    exact Set.mem_sUnion.mpr ⟨_, Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨i, his, rfl⟩), hxi⟩
  obtain ⟨Z, hZ, hCZ⟩ := isIrreducible_iff_sUnion_isClosed.mp hirred
    (s.image (fun i ↦ (nodeClosed (t := t) {i} : Set X)))
    (by intro Z hZ; obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hZ;
        exact (nodeClosed (t := t) {i}).isClosed) hcover
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hZ
  have haxis : (nodeClosed (t := t) {i} : Set X) ⊆ D.support := by
    rw [nodeDivisor_support]
    exact Set.subset_iUnion_of_subset i (Set.subset_iUnion_of_subset hi (Set.Subset.refl _))
  let g : nodeClosed (t := t) {i} → D.support :=
    fun x ↦ ⟨x.val, haxis x.property⟩
  have hg : Continuous g := continuous_subtype_val.subtype_mk _
  let : IrreducibleSpace (nodeClosed (t := t) {i}) :=
    Subtype.irreducibleSpace (nodeClosed_isIrreducible {i})
  have hgirred : IsIrreducible (g '' Set.univ) :=
    (IrreducibleSpace.isIrreducible_univ _).image g hg.continuousOn
  have hSg : S ⊆ g '' Set.univ := by
    intro y hy
    have hyaxis := hCZ (hC ▸ Set.mem_image_of_mem Subtype.val hy)
    exact ⟨⟨y.val, hyaxis⟩, Set.mem_univ _, Subtype.ext rfl⟩
  have hgS : g '' Set.univ ⊆ S := hS.2 hgirred hSg
  refine ⟨i, hi, Closeds.ext (Set.Subset.antisymm hCZ ?_)⟩
  intro x hx
  rw [← hC]
  exact Set.mem_image_of_mem Subtype.val (hgS ⟨⟨x, hx⟩, Set.mem_univ _, rfl⟩)

/-- The unique coordinate index of an actual irreducible component. -/
def componentIndex (s : Finset (Fin 2)) (C : DivisorComponent (nodeDivisor (t := t) s)) : Fin 2 :=
  (component_eq_nodeClosed s C).choose

omit [IsRegularRing A] [IsRegularRing (ParameterQuotient t)] in
theorem componentIndex_mem (s : Finset (Fin 2))
    (C : DivisorComponent (nodeDivisor (t := t) s)) : componentIndex s C ∈ s :=
  (component_eq_nodeClosed s C).choose_spec.1

omit [IsRegularRing A] [IsRegularRing (ParameterQuotient t)] in
theorem componentIndex_closed (s : Finset (Fin 2))
    (C : DivisorComponent (nodeDivisor (t := t) s)) :
    C.val = nodeClosed {componentIndex s C} :=
  (component_eq_nodeClosed s C).choose_spec.2

omit [IsRegularRing A] [IsRegularRing (ParameterQuotient t)] in
theorem componentIndex_injective (s : Finset (Fin 2)) :
    Function.Injective (componentIndex (t := t) s) := by
  intro C C' h
  apply Subtype.ext
  rw [componentIndex_closed s C, componentIndex_closed s C', h]

omit [IsRegularRing A] [IsRegularRing (ParameterQuotient t)] in
theorem vanishingIdeal_nodeClosed (s : Finset (Fin 2)) :
    Scheme.IdealSheafData.vanishingIdeal (nodeClosed (t := t) s) =
      specIdealSheaf (Node A t) (nodeIdeal t s) := by
  apply idealSheaf_eq_of_radical_of_support_eq
  · exact radical_vanishingIdeal _
  · rw [specIdealSheaf_radical, (nodeIdealPrime (t := t) s).isRadical.radical]
  · rfl

omit [IsRegularRing A] [IsRegularRing (ParameterQuotient t)] in
/-- The native scheme-theoretic intersection is the coordinate ideal of its
actual distinct components, without taking an extra radical. -/
theorem componentIntersection_nodeDivisor (s : Finset (Fin 2))
    (J : Finset (DivisorComponent (nodeDivisor (t := t) s))) :
    componentIntersection (nodeDivisor s) J =
      specIdealSheaf (Node A t) (nodeIdeal t (J.image (componentIndex s))) := by
  classical
  have hcoord : (⨆ C ∈ J, nodeIdeal t {componentIndex s C}) =
      nodeIdeal t (J.image (componentIndex s)) := by
    apply le_antisymm
    · refine iSup_le fun C ↦ iSup_le fun hC ↦ nodeIdeal_mono t ?_
      simpa only [Finset.singleton_subset_iff] using Finset.mem_image_of_mem (componentIndex s) hC
    · apply Ideal.span_le.mpr
      rintro _ ⟨i, hi, rfl⟩
      obtain ⟨C, hC, rfl⟩ := Finset.mem_image.mp hi
      have hinc : nodeIdeal t {componentIndex s C} ≤
          ⨆ C ∈ J, nodeIdeal t {componentIndex s C} :=
        le_iSup_of_le C (le_iSup_of_le hC le_rfl)
      exact hinc (Ideal.subset_span (Set.mem_image_of_mem (coordinate t) (Finset.mem_singleton_self _)))
  calc
    componentIntersection (nodeDivisor s) J =
        ⨆ C ∈ J, specIdealSheaf (Node A t) (nodeIdeal t {componentIndex s C}) := by
      simp only [componentIntersection, componentIndex_closed s, vanishingIdeal_nodeClosed]
    _ = specIdealSheaf (Node A t)
        (⨆ C ∈ J, nodeIdeal t {componentIndex s C}) :=
      ((specIdealSheafEquiv (Node A t)).symm.map_iSup₂ _).symm
    _ = _ := congrArg _ hcoord

omit [IsRegularRing A] [IsRegularRing (ParameterQuotient t)] in
theorem nodeDivisor_isReduced (s : Finset (Fin 2)) :
    IsReduced (nodeDivisor (t := t) s).subscheme := by
  have hrad : (nodeDivisor (t := t) s).radical = nodeDivisor s := by
    rw [nodeDivisor, specIdealSheaf_radical, (nodeProduct_isRadical s).radical]
  simpa only [hrad] using isReduced_radical_subscheme (nodeDivisor (t := t) s)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
omit [IsRegularRing A] [(Ideal.span {t}).IsPrime] [IsRegularRing (ParameterQuotient t)] in
theorem nodeDivisor_isEffectiveCartier (s : Finset (Fin 2)) :
    IsEffectiveCartierDivisor (nodeDivisor (t := t) s) := by
  intro x
  let e : Node A t ≃+* Γ(Spec (CommRingCat.of (Node A t)), ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of (Node A t))).symm.commRingCatIsoToRingEquiv
  have hprod : (∏ i ∈ s, (coordinate t i : Node A t)) ≠ 0 := by
    exact Finset.prod_ne_zero_iff.mpr (fun i _ ↦ Algebra.NodeDomain.nodeCoordinate_ne_zero t (Fact.out : t ≠ 0) i)
  have hprodRegular : IsRegular (e (∏ i ∈ s, coordinate t i)) := by
    constructor
    · intro a b hab
      apply e.symm.injective
      apply mul_left_cancel₀ hprod
      simpa only [map_mul, e.symm_apply_apply] using congrArg e.symm hab
    · intro a b hab
      apply e.symm.injective
      apply mul_right_cancel₀ hprod
      simpa only [map_mul, e.symm_apply_apply] using congrArg e.symm hab
  refine ⟨⟨⊤, isAffineOpen_top _⟩, trivial, e (∏ i ∈ s, coordinate t i), hprodRegular, ?_⟩
  rw [nodeDivisor, specIdealSheaf_ideal_top, Ideal.map_span, Set.image_singleton]
  rfl

/-- Every actual standard coordinate divisor has strict normal crossings,
including all its genuine scheme-theoretic component intersections. -/
theorem isStrictNormalCrossings_nodeDivisor (s : Finset (Fin 2))
    (hparam : ∀ (p : Ideal A) [p.IsPrime], t ∈ p →
      algebraMap A (Localization.AtPrime p) t ∉ IsLocalRing.maximalIdeal (Localization.AtPrime p) ^ 2) :
    IsStrictNormalCrossings (nodeDivisor (t := t) s) := by
  refine ⟨nodeDivisor_isEffectiveCartier s, nodeDivisor_isReduced s,
    ?_, ?_, ?_⟩
  · intro x _
    exact RegularNode.isRegularScheme_nodeQuotient t hparam x
  · intro J hJ
    rw [componentIntersection_nodeDivisor]
    let : IsRegularRing (Node A t ⧸ nodeIdeal t (J.image (componentIndex s))) :=
      nodeIdeal_quotient_isRegularRing t _ (hJ.image (componentIndex s))
    exact CoordinateSNC.isRegularScheme_specIdealSheaf_subscheme _ _
  · intro J _
    rw [componentIntersection_nodeDivisor]
    have hcard : (J.image (componentIndex s)).card = J.card :=
      Finset.card_image_of_injective _ (componentIndex_injective s)
    rw [← hcard]
    exact nodeClosed_hasPureCodimension _


end Hironaka.Geometry.MonomialBlowupRegularBaseSNCNodeBoundary

namespace Hironaka.Geometry.MonomialBlowupRegularBaseSNCNodeBoundary

open Algebra.NodeBlowupChart Algebra.NodeNormalCoordinates
open SpecIdealSheaf ReducedClosedSubscheme MonomialBlowupRegularBaseSNCParameters

universe u
variable {A : Type u} [CommRing A]

/-- The actual coefficient inverse-image principal ideal, retaining its literal equation. -/
def coefficientDivisor (t : A) : (Spec (CommRingCat.of (Node A t))).IdealSheafData :=
  specIdealSheaf (Node A t) (Ideal.span {algebraMap A (Node A t) t})

/-- Exact ideal-sheaf equality with the actual native coefficient pullback. -/
theorem coefficientDivisor_eq_comap (t : A) : coefficientDivisor t =
    (specIdealSheaf A (Ideal.span {t})).comap
      (Spec.map (CommRingCat.ofHom (algebraMap A (Node A t)))) := by
  rw [specIdealSheaf_comap, Ideal.map_span, Set.image_singleton]
  rfl

/-- The original coefficient ideal is literally the original two-axis product ideal. -/
theorem coefficientDivisor_eq_nodeDivisor (t : A) :
    coefficientDivisor t = nodeDivisor (t := t) Finset.univ := by
  unfold coefficientDivisor nodeDivisor
  rw [Fin.prod_univ_two]
  have h : coordinate t 0 * coordinate t 1 = algebraMap A (Node A t) t :=
    Algebra.NodeDomain.nodeCoordinateProduct t
  rw [h]

variable [IsRegularRing A] [IsDomain A]

/-- A genuine SNC component equation internally gives a reduced actual coefficient boundary on the node. -/
theorem coefficientDivisor_isReduced
    (D : (Spec (CommRingCat.of A)).IdealSheafData) (hD : IsStrictNormalCrossings D)
    (C : DivisorComponent D) (t : A)
    (heq : specIdealSheaf A (Ideal.span {t}) = Scheme.IdealSheafData.vanishingIdeal C.val) :
    IsReduced (coefficientDivisor t).subscheme := by
  obtain ⟨hp, _, hq⟩ := component_equation_data D hD C t heq
  let := hp
  let := hq
  let : Fact (t ≠ 0) := ⟨component_equation_ne_zero D hD C t heq⟩
  rw [coefficientDivisor_eq_nodeDivisor]
  exact nodeDivisor_isReduced Finset.univ

/-- The actual coefficient pullback of a genuine SNC component is SNC, with no caller node certificates. -/
theorem coefficientDivisor_isStrictNormalCrossings
    (D : (Spec (CommRingCat.of A)).IdealSheafData) (hD : IsStrictNormalCrossings D)
    (C : DivisorComponent D) (t : A)
    (heq : specIdealSheaf A (Ideal.span {t}) = Scheme.IdealSheafData.vanishingIdeal C.val) :
    IsStrictNormalCrossings (coefficientDivisor t) := by
  obtain ⟨hp, _, hq⟩ := component_equation_data D hD C t heq
  let := hp
  let := hq
  let : Fact (t ≠ 0) := ⟨component_equation_ne_zero D hD C t heq⟩
  rw [coefficientDivisor_eq_nodeDivisor]
  apply isStrictNormalCrossings_nodeDivisor
  exact component_equation_parameter D hD C t heq

end Hironaka.Geometry.MonomialBlowupRegularBaseSNCNodeBoundary
