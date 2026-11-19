import Hironaka.Geometry.MonomialBlowupTowerBoundaryPolynomial

/-! Exact reduced coordinate boundary on each actual finished node. -/

noncomputable section

open AlgebraicGeometry CategoryTheory MvPolynomial

namespace Hironaka.Geometry.MonomialBlowupTowerBoundaryFinished

open Algebra.NodeBlowupChart SpecIdealSheaf CoordinateSNC ReducedClosedSubscheme
open MonomialBlowupTowerBoundaryPolynomial

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (K : Type u) [Field K] {ι : Type u} [DecidableEq ι]

/-- The actual monomial, including its original multiplicities. -/
def monomial (l : List ι) : Base K (ι := ι) := (l.map (fun i ↦ X i)).prod

/-- The literal coefficient inverse-image ideal before reduction. -/
def chartRawBoundary (l : List ι) (i : ι) :
    (Spec (CommRingCat.of (Chart K i))).IdealSheafData :=
  specIdealSheaf (Chart K i) (Ideal.span {algebraMap (Base K (ι := ι)) (Chart K i) (monomial K l)})

/-- The actual reduced coefficient boundary. -/
def chartBoundary (l : List ι) (i : ι) :
    (Spec (CommRingCat.of (Chart K i))).IdealSheafData := (chartRawBoundary K l i).radical

variable [Finite ι]

/-- Exactly the node variables and the surviving coordinates occurring in the original list. -/
def boundaryVariables (l : List ι) (i : ι) : Finset (Variables i) := by
  classical
  letI := Fintype.ofFinite (Variables i)
  exact Finset.univ.filter (Sum.elim (fun _ ↦ True) (fun j ↦ j.val ∈ l))

omit [DecidableEq ι] in
@[simp]
theorem mem_boundaryVariables_left (l : List ι) (i : ι) (j : Fin 2) :
    Sum.inl j ∈ boundaryVariables l i := by
  classical
  simp [boundaryVariables]

omit [DecidableEq ι] in
@[simp]
theorem mem_boundaryVariables_right (l : List ι) (i : ι) (j : {j : ι // j ≠ i}) :
    Sum.inr j ∈ boundaryVariables l i ↔ j.val ∈ l := by
  classical
  simp [boundaryVariables]

omit [Finite ι] in
private theorem evaluated_monomial_mem_iff (l : List ι) (i : ι)
    (p : Ideal (PolynomialChart K i)) [p.IsPrime] :
    baseEvaluation K i (monomial K l) ∈ p ↔
      ∃ j ∈ l, baseEvaluation K i (X j) ∈ p := by
  induction l with
  | nil => simp [monomial, Ideal.one_notMem]
  | cons j l ih =>
    simp only [monomial, List.map_cons, List.prod_cons, map_mul]
    rw [Ideal.IsPrime.mul_mem_iff_mem_or_mem (inferInstance : p.IsPrime)]
    simpa only [monomial, List.mem_cons, exists_eq_or_imp] using or_congr Iff.rfl ih

/-- Prime support of the exact evaluated monomial, with all multiplicities retained. -/
theorem evaluated_monomial_mem_iff_coordinate (l : List ι) (i : ι) (hi : i ∈ l)
    (p : Ideal (PolynomialChart K i)) [p.IsPrime] :
    baseEvaluation K i (monomial K l) ∈ p ↔
      ∃ j ∈ boundaryVariables l i, (X j : PolynomialChart K i) ∈ p := by
  rw [evaluated_monomial_mem_iff]
  constructor
  · rintro ⟨j, hj, hmem⟩
    by_cases hji : j = i
    · subst j
      simp [baseEvaluation, Ideal.IsPrime.mul_mem_iff_mem_or_mem] at hmem
      rcases hmem with h | h
      · exact ⟨Sum.inl 0, mem_boundaryVariables_left l i 0, h⟩
      · exact ⟨Sum.inl 1, mem_boundaryVariables_left l i 1, h⟩
    · exact ⟨Sum.inr ⟨j, hji⟩, (mem_boundaryVariables_right l i _).mpr hj,
        by simpa [baseEvaluation, hji] using hmem⟩
  · rintro ⟨j, hj, hmem⟩
    cases j with
    | inl j =>
      refine ⟨i, hi, ?_⟩
      simp [baseEvaluation, Ideal.IsPrime.mul_mem_iff_mem_or_mem]
      fin_cases j
      · exact Or.inl hmem
      · exact Or.inr hmem
    | inr j =>
      exact ⟨j.val, (mem_boundaryVariables_right l i j).mp hj,
        by simpa [baseEvaluation, j.property] using hmem⟩

/-- The reduced actual boundary becomes the exact squarefree coordinate divisor. -/
theorem chartBoundary_comap_polynomial (l : List ι) (i : ι) (hi : i ∈ l) :
    (chartBoundary K l i).comap (polynomialIso K i).inv =
      coordinateDivisor (k := K) (boundaryVariables l i) := by
  rw [chartBoundary, radical_comap_open]
  let : IsReduced ((chartRawBoundary K l i).comap (polynomialIso K i).inv).radical.subscheme :=
    isReduced_radical_subscheme _
  let : IsReduced (coordinateDivisor (k := K) (boundaryVariables l i)).subscheme :=
    coordinateDivisor_isReduced _
  apply idealSheaf_eq_of_isReduced_of_support_eq
  rw [Scheme.IdealSheafData.support_radical, chartRawBoundary, polynomialIso_inv,
    specIdealSheaf_comap, Ideal.map_span, Set.image_singleton]
  have hgen : (polynomialEquiv K i).toRingEquiv.toRingHom
      (algebraMap (Base K (ι := ι)) (Chart K i) (monomial K l)) =
      baseEvaluation K i (monomial K l) := polynomialEquiv_base K i _
  rw [hgen]
  apply TopologicalSpace.Closeds.ext
  rw [specIdealSheaf_support, coordinateDivisor, specIdealSheaf_support]
  ext p
  let : p.asIdeal.IsPrime := p.isPrime
  simp only [PrimeSpectrum.zeroLocus_span, PrimeSpectrum.mem_zeroLocus,
    Set.singleton_subset_iff]
  change baseEvaluation K i (monomial K l) ∈ p.asIdeal ↔
    (∏ j ∈ boundaryVariables l i, (X j : PolynomialChart K i)) ∈ p.asIdeal
  rw [evaluated_monomial_mem_iff_coordinate K l i hi p.asIdeal,
    Ideal.IsPrime.prod_mem_iff]

/-- A genuine SNC divisor on every finished node, without any supplied component data. -/
theorem chartBoundary_isStrictNormalCrossings (l : List ι) (i : ι) (hi : i ∈ l) :
    IsStrictNormalCrossings (chartBoundary K l i) := by
  apply (SNCIso.isStrictNormalCrossings_comap_iff (polynomialIso K i).symm
    (chartBoundary K l i)).mp
  change IsStrictNormalCrossings ((chartBoundary K l i).comap (polynomialIso K i).inv)
  rw [chartBoundary_comap_polynomial K l i hi]
  exact isStrictNormalCrossings_coordinateDivisor _

end Hironaka.Geometry.MonomialBlowupTowerBoundaryFinished
