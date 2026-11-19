import Hironaka.Geometry.PolynomialNodeResolution
import Hironaka.Geometry.CoordinateSNC
import Hironaka.Geometry.SNCIso

/-!
# The exact polynomial boundary on the genuine node charts

Quotient elimination preserves the actual chart structure maps. The boundary
is the actual inverse-image ideal, without replacing it by its radical.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MvPolynomial

namespace Hironaka.PolynomialNodeBoundary

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Algebra.NodeBlowupChart Geometry.SpecIdealSheaf Geometry.CoordinateSNC

variable (K : Type u) [Field K]

abbrev Base := MvPolynomial (Fin 2) K
abbrev PolynomialChart := MvPolynomial (Fin 3) K
abbrev Chart (k : Fin 2) := Node (Base K) (X k)

/-- The coefficient coordinate not eliminated by the node relation. -/
def otherCoordinate (k : Fin 2) : Fin 2 := Equiv.swap 0 1 k

/-- The coefficient substitution replaces the parameter by the product of node coordinates. -/
def baseEvaluation (k : Fin 2) : Base K →ₐ[K] PolynomialChart K :=
  aeval (fun i => if i = k then X 0 * X 1 else X 2)

/-- Polynomial evaluation before passing to the actual node quotient. -/
def nodePolynomialEvaluation (k : Fin 2) :
    MvPolynomial (Fin 2) (Base K) →ₐ[K] PolynomialChart K :=
  aevalTower (baseEvaluation K k) ![X 0, X 1]

private theorem nodePolynomialEvaluation_ideal (k : Fin 2) :
    Algebra.NodeChart.uChartIdeal (Base K) (X k) ≤
      RingHom.ker (nodePolynomialEvaluation K k).toRingHom := by
  apply Ideal.span_le.mpr
  rintro _F (rfl : _F = _)
  change nodePolynomialEvaluation K k (X 0 * X 1 - C (X k)) = 0
  simp [nodePolynomialEvaluation, baseEvaluation]

/-- The actual node quotient maps to the three-variable polynomial algebra. -/
def chartForward (k : Fin 2) : Chart K k →ₐ[K] PolynomialChart K :=
  Ideal.Quotient.liftₐ _ (nodePolynomialEvaluation K k)
    (fun _ hF => nodePolynomialEvaluation_ideal K k hF)

@[simp]
theorem chartForward_mk (k : Fin 2) (F : MvPolynomial (Fin 2) (Base K)) :
    chartForward K k (Ideal.Quotient.mk _ F) = nodePolynomialEvaluation K k F := rfl

@[simp]
theorem chartForward_coordinate (k i : Fin 2) :
    chartForward K k (coordinate (X k : Base K) i) = ![X 0, X 1] i := by
  simp [coordinate, nodePolynomialEvaluation]

@[simp]
theorem chartForward_base (k : Fin 2) (a : Base K) :
    chartForward K k (algebraMap (Base K) (Chart K k) a) = baseEvaluation K k a := by
  change chartForward K k (Ideal.Quotient.mk _ (C a)) = _
  simp [nodePolynomialEvaluation]

/-- The inverse polynomial substitution uses the actual quotient coordinates. -/
def chartBackward (k : Fin 2) : PolynomialChart K →ₐ[K] Chart K k :=
  aeval ![coordinate (X k : Base K) 0, coordinate (X k : Base K) 1,
    algebraMap (Base K) (Chart K k) (X (otherCoordinate k))]

@[simp]
theorem chartCoordinateProduct (k : Fin 2) :
    coordinate (X k : Base K) 0 * coordinate (X k : Base K) 1 =
      algebraMap (Base K) (Chart K k) (X k) :=
  Algebra.NodeDomain.nodeCoordinateProduct _

private theorem chartBackward_baseEvaluation (k : Fin 2) :
    (chartBackward K k).comp (baseEvaluation K k) =
      IsScalarTower.toAlgHom K (Base K) (Chart K k) := by
  ext i
  fin_cases k <;> fin_cases i <;>
    simp [chartBackward, baseEvaluation, otherCoordinate]

private theorem chartForward_backward (k : Fin 2) :
    (chartForward K k).comp (chartBackward K k) = AlgHom.id K _ := by
  ext i
  fin_cases i
  · simp [chartBackward]
  · simp [chartBackward]
  · fin_cases k <;> simp [chartBackward, baseEvaluation, otherCoordinate]

private theorem chartBackward_forward (k : Fin 2) :
    (chartBackward K k).comp (chartForward K k) = AlgHom.id K _ := by
  apply Ideal.Quotient.algHom_ext
  apply AlgHom.coe_ringHom_injective
  apply MvPolynomial.ringHom_ext
  · intro a
    simpa only [AlgHom.comp_apply, AlgHom.id_apply, AlgHom.coe_toRingHom,
      Ideal.Quotient.mkₐ_eq_mk, chartForward_mk, nodePolynomialEvaluation, aevalTower_C,
      RingHom.comp_apply, IsScalarTower.toAlgHom_apply, ← Ideal.Quotient.mk_algebraMap,
      MvPolynomial.algebraMap_eq] using AlgHom.congr_fun (chartBackward_baseEvaluation K k) a
  · intro i
    fin_cases i <;> simp [nodePolynomialEvaluation, chartBackward, coordinate]

/-- Genuine elimination of the base parameter identifies the entire node quotient with affine three-space. -/
def chartPolynomialEquiv (k : Fin 2) : Chart K k ≃ₐ[K] PolynomialChart K :=
  AlgEquiv.ofAlgHom (chartForward K k) (chartBackward K k)
    (chartForward_backward K k) (chartBackward_forward K k)

@[simp]
theorem chartPolynomialEquiv_coordinate (k i : Fin 2) :
    chartPolynomialEquiv K k (coordinate (X k : Base K) i) = ![X 0, X 1] i :=
  chartForward_coordinate K k i

@[simp]
theorem chartPolynomialEquiv_base (k : Fin 2) (a : Base K) :
    chartPolynomialEquiv K k (algebraMap (Base K) (Chart K k) a) = baseEvaluation K k a :=
  chartForward_base K k a

/-- The actual native spectra are identified by the proved quotient algebra equivalence. -/
def chartPolynomialIso (k : Fin 2) :
    Spec (CommRingCat.of (Chart K k)) ≅ Spec (CommRingCat.of (PolynomialChart K)) :=
  Scheme.Spec.mapIso (chartPolynomialEquiv K k).toRingEquiv.toCommRingCatIso.symm.op

@[simp]
theorem chartPolynomialIso_hom (k : Fin 2) :
    (chartPolynomialIso K k).hom = Spec.map
      (CommRingCat.ofHom (chartPolynomialEquiv K k).symm.toRingHom) := rfl

@[simp]
theorem chartPolynomialIso_inv (k : Fin 2) :
    (chartPolynomialIso K k).inv = Spec.map
      (CommRingCat.ofHom (chartPolynomialEquiv K k).toRingHom) := rfl

/-- The crossing divisor is the actual ideal sheaf `(x₀*x₁)` on the polynomial base. -/
def baseBoundary : (Spec (CommRingCat.of (Base K))).IdealSheafData :=
  specIdealSheaf (Base K) (Ideal.span {(X 0 * X 1 : Base K)})

/-- The exact inverse-image boundary along the actual coefficient map of a smaller-node chart. -/
def chartBoundary (k : Fin 2) : (Spec (CommRingCat.of (Chart K k))).IdealSheafData :=
  (baseBoundary K).comap (Spec.map (CommRingCat.ofHom (algebraMap (Base K) (Chart K k))))

/-- Elimination sends the original boundary generator to the exact three-coordinate product. -/
theorem baseBoundary_generator_image (k : Fin 2) :
    chartPolynomialEquiv K k (algebraMap (Base K) (Chart K k) (X 0 * X 1)) =
      ∏ i : Fin 3, (X i : PolynomialChart K) := by
  rw [chartPolynomialEquiv_base]
  fin_cases k <;> simp [baseEvaluation, Fin.prod_univ_succ] <;> ring

/-- The exact chart boundary is the pullback of the coordinate-product divisor along the chart isomorphism. -/
theorem chartBoundary_eq_coordinate_comap (k : Fin 2) :
    chartBoundary K k =
      (coordinateDivisor (k := K) (Finset.univ : Finset (Fin 3))).comap
        (chartPolynomialIso K k).hom := by
  have hgen : algebraMap (Base K) (Chart K k) (X 0 * X 1) =
      (chartPolynomialEquiv K k).symm (∏ i : Fin 3, (X i : PolynomialChart K)) := by
    apply (chartPolynomialEquiv K k).injective
    rw [AlgEquiv.apply_symm_apply]
    exact baseBoundary_generator_image K k
  change (specIdealSheaf (Base K) (Ideal.span {(X 0 * X 1 : Base K)})).comap
      (Spec.map (CommRingCat.ofHom (algebraMap (Base K) (Chart K k)))) =
    (specIdealSheaf (PolynomialChart K) (Ideal.span {∏ i : Fin 3, (X i : PolynomialChart K)})).comap
      (Spec.map (CommRingCat.ofHom (chartPolynomialEquiv K k).symm.toRingHom))
  rw [specIdealSheaf_comap, specIdealSheaf_comap, Ideal.map_span, Ideal.map_span,
    Set.image_singleton, Set.image_singleton]
  rw [hgen]
  rfl

/-- In polynomial coordinates the actual pulled-back ideal sheaf equals `(y₀*y₁*y₂)` itself. -/
theorem chartBoundary_comap_polynomial (k : Fin 2) :
    (chartBoundary K k).comap (chartPolynomialIso K k).inv =
      coordinateDivisor (k := K) (Finset.univ : Finset (Fin 3)) := by
  rw [chartBoundary_eq_coordinate_comap, ← Scheme.IdealSheafData.comap_comp,
    Iso.inv_hom_id, Scheme.IdealSheafData.comap_id]

/-- The exact smaller-node chart ideal is generated by its two node coordinates and the other base coordinate. -/
theorem chartBoundary_eq_product_ideal (k : Fin 2) :
    chartBoundary K k = specIdealSheaf (Chart K k) (Ideal.span
      {coordinate (X k : Base K) 0 * coordinate (X k : Base K) 1 *
        algebraMap (Base K) (Chart K k) (X (otherCoordinate k))}) := by
  have hgen : algebraMap (Base K) (Chart K k) (X 0 * X 1) =
      coordinate (X k : Base K) 0 * coordinate (X k : Base K) 1 *
        algebraMap (Base K) (Chart K k) (X (otherCoordinate k)) := by
    rw [chartCoordinateProduct]
    fin_cases k <;> simp [otherCoordinate, mul_comm] <;> exact map_mul _ _ _
  change (specIdealSheaf (Base K) (Ideal.span {(X 0 * X 1 : Base K)})).comap
    (Spec.map (CommRingCat.ofHom (algebraMap (Base K) (Chart K k)))) = _
  rw [specIdealSheaf_comap, Ideal.map_span, Set.image_singleton, hgen]

local instance coordinateFact (i : Fin 2) : Fact ((X i : Base K) ≠ 0) := ⟨X_ne_zero i⟩

abbrev CrossingNode := Node (Base K) ((X 0 : Base K) * X 1)

/-- The actual original crossing-node morphism to its polynomial base. -/
def originalNodeToBase : PolynomialNodeResolution.polynomialNode K (0 : Fin 2) 1 ⟶
    Spec (CommRingCat.of (Base K)) :=
  Spec.map (CommRingCat.ofHom (algebraMap (Base K) (CrossingNode K)))

/-- The exact inverse-image boundary on the actual native polynomial-node blowup. -/
def resolvedBoundary : (PolynomialNodeResolution.resolvedNode K (0 : Fin 2) 1).IdealSheafData :=
  (baseBoundary K).comap
    (PolynomialNodeResolution.resolutionMorphism K (0 : Fin 2) 1 ≫ originalNodeToBase K)

/-- The already constructed genuine coordinate-chart immersion, with nonzero facts internalized. -/
def nativeUChartMap : Spec (CommRingCat.of (Chart K 0)) ⟶
    PolynomialNodeResolution.resolvedNode K (0 : Fin 2) 1 :=
  uChartInclusion (X 0 : Base K) (X 1)

/-- The already constructed genuine parameter-chart immersion, with nonzero facts internalized. -/
def nativeTChartMap : Spec (CommRingCat.of (Chart K 1)) ⟶
    PolynomialNodeResolution.resolvedNode K (0 : Fin 2) 1 :=
  tChartInclusion (X 0 : Base K) (X 1)

/-- The actual coordinate-chart composite to the base retains the canonical coefficient map. -/
theorem nativeUChartMap_toBase :
    nativeUChartMap K ≫ PolynomialNodeResolution.resolutionMorphism K (0 : Fin 2) 1 ≫
      originalNodeToBase K =
        Spec.map (CommRingCat.ofHom (algebraMap (Base K) (Chart K 0))) := by
  dsimp only [nativeUChartMap, PolynomialNodeResolution.resolutionMorphism,
    PolynomialNodeResolution.polynomialNodeCenter, originalNodeToBase]
  rw [← Category.assoc, uChartInclusion_structure, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  exact (uChartOriginalMap (X 0 : Base K) (X 1)).commutes a

/-- The actual parameter-chart composite to the base retains the canonical coefficient map. -/
theorem nativeTChartMap_toBase :
    nativeTChartMap K ≫ PolynomialNodeResolution.resolutionMorphism K (0 : Fin 2) 1 ≫
      originalNodeToBase K =
        Spec.map (CommRingCat.ofHom (algebraMap (Base K) (Chart K 1))) := by
  dsimp only [nativeTChartMap, PolynomialNodeResolution.resolutionMorphism,
    PolynomialNodeResolution.polynomialNodeCenter, originalNodeToBase]
  rw [← Category.assoc, tChartInclusion_structure, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  exact (tChartOriginalMap (X 0 : Base K) (X 1)).commutes a

/-- Pullback along the actual native coordinate chart gives its canonical exact coefficient boundary. -/
theorem resolvedBoundary_comap_uChart :
    (resolvedBoundary K).comap (nativeUChartMap K) = chartBoundary K 0 := by
  dsimp only [resolvedBoundary]
  rw [← Scheme.IdealSheafData.comap_comp, nativeUChartMap_toBase]
  rfl

/-- Pullback along the actual native parameter chart gives its canonical exact coefficient boundary. -/
theorem resolvedBoundary_comap_tChart :
    (resolvedBoundary K).comap (nativeTChartMap K) = chartBoundary K 1 := by
  dsimp only [resolvedBoundary]
  rw [← Scheme.IdealSheafData.comap_comp, nativeTChartMap_toBase]
  rfl

/-- The exact native coordinate-chart pullback becomes the coordinate product in its polynomial coordinates. -/
theorem resolvedBoundary_uChart_polynomial :
    ((resolvedBoundary K).comap (nativeUChartMap K)).comap (chartPolynomialIso K 0).inv =
      coordinateDivisor (k := K) (Finset.univ : Finset (Fin 3)) := by
  rw [resolvedBoundary_comap_uChart, chartBoundary_comap_polynomial]

/-- The exact native parameter-chart pullback becomes the coordinate product in its polynomial coordinates. -/
theorem resolvedBoundary_tChart_polynomial :
    ((resolvedBoundary K).comap (nativeTChartMap K)).comap (chartPolynomialIso K 1).inv =
      coordinateDivisor (k := K) (Finset.univ : Finset (Fin 3)) := by
  rw [resolvedBoundary_comap_tChart, chartBoundary_comap_polynomial]

/-- The native coordinate-chart boundary is exactly `(u*w*x₁)`, before taking any radical. -/
theorem resolvedBoundary_uChart_ideal :
    (resolvedBoundary K).comap (nativeUChartMap K) = specIdealSheaf (Chart K 0) (Ideal.span
      {coordinate (X 0 : Base K) 0 * coordinate (X 0 : Base K) 1 *
        algebraMap (Base K) (Chart K 0) (X 1)}) := by
  rw [resolvedBoundary_comap_uChart]
  simpa [otherCoordinate] using chartBoundary_eq_product_ideal K 0

/-- The native parameter-chart boundary is exactly `(x₀*v*z)`, before taking any radical. -/
theorem resolvedBoundary_tChart_ideal :
    (resolvedBoundary K).comap (nativeTChartMap K) = specIdealSheaf (Chart K 1) (Ideal.span
      {algebraMap (Base K) (Chart K 1) (X 0) *
        coordinate (X 1 : Base K) 0 * coordinate (X 1 : Base K) 1}) := by
  rw [resolvedBoundary_comap_tChart, chartBoundary_eq_product_ideal]
  apply congrArg (specIdealSheaf (Chart K 1))
  apply congrArg Ideal.span
  apply congrArg Set.singleton
  change coordinate (X 1 : Base K) 0 * coordinate (X 1 : Base K) 1 *
      algebraMap (Base K) (Chart K 1) (X 0) =
    algebraMap (Base K) (Chart K 1) (X 0) *
      coordinate (X 1 : Base K) 0 * coordinate (X 1 : Base K) 1
  exact (mul_comm (_ * _) _).trans (mul_assoc _ _ _).symm

/-- Exact SNC of each canonical chart boundary follows from actual polynomial coordinates. -/
theorem chartBoundary_isStrictNormalCrossings (k : Fin 2) :
    IsStrictNormalCrossings (chartBoundary K k) := by
  rw [chartBoundary_eq_coordinate_comap]
  exact Geometry.SNCIso.isStrictNormalCrossings_comap (chartPolynomialIso K k)
    (coordinateDivisor (k := K) (Finset.univ : Finset (Fin 3)))
    (isStrictNormalCrossings_coordinateDivisor _)

/-- The actual inverse-image boundary has strict normal crossings on the genuine coordinate chart. -/
theorem resolvedBoundary_uChart_isStrictNormalCrossings :
    IsStrictNormalCrossings ((resolvedBoundary K).comap (nativeUChartMap K)) := by
  rw [resolvedBoundary_comap_uChart]
  exact chartBoundary_isStrictNormalCrossings K 0

/-- The actual inverse-image boundary has strict normal crossings on the genuine parameter chart. -/
theorem resolvedBoundary_tChart_isStrictNormalCrossings :
    IsStrictNormalCrossings ((resolvedBoundary K).comap (nativeTChartMap K)) := by
  rw [resolvedBoundary_comap_tChart]
  exact chartBoundary_isStrictNormalCrossings K 1

end Hironaka.PolynomialNodeBoundary
