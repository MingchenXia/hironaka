import Hironaka.Geometry.ProjectiveSecantProjectionCoordinates

/-!
# Actual original source-chart prime and native discarded derivative nonmembership
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousLocalization

namespace Hironaka.Geometry.ProjectiveSecant

open ProjectiveIdeal ProjectiveProjection ProjectiveProjectionCenter ProjectiveRationalPointCoordinates
open Algebra.ProjectiveSecant Algebra.ProjectiveLinearCoordinates

universe u

attribute [local instance] MvPolynomial.gradedAlgebra homogeneousChartAlgebra

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (k : Type u) [Field k] (n : ℕ)

/-- The whole native polynomial chart detects an arbitrary homogeneous equation by the exact original affine dehomogenization; multiplying by the chart coordinate makes the native positive-degree API apply even in degree zero. -/
theorem coordinateChartInclusion_preimage_mul_equation (j : Fin (n + 2))
    {d : ℕ} {H : MvPolynomial (Fin (n + 2)) k} (hH : H.IsHomogeneous d) :
    Segre.coordinateChartInclusion (R := k) j ⁻¹ᵁ
        Proj.basicOpen (ProjectiveGrading k (n + 1)) (MvPolynomial.X j * H) =
      PrimeSpectrum.basicOpen (coordinateDehom j H) := by
  have hG : MvPolynomial.X j * H ∈ ProjectiveGrading k (n + 1) (d + 1) := by
    change (MvPolynomial.X j * H).IsHomogeneous (d + 1)
    simpa only [Nat.add_comm] using (MvPolynomial.isHomogeneous_X k j).mul hH
  rw [Segre.coordinateChartInclusion_eq, Scheme.Hom.comp_preimage,
    Proj.awayι_preimage_basicOpen (𝒜 := ProjectiveGrading k (n + 1))
      (MvPolynomial.isHomogeneous_X k j) (by decide : 0 < (1 : ℕ)) hG (Nat.succ_pos d),
    SpecMap_preimage_basicOpen]
  congr 1
  change homogeneousChartDehom j
    (Away.mk (ProjectiveGrading k (n + 1)) (MvPolynomial.isHomogeneous_X k j)
      (d + 1) ((MvPolynomial.X j * H) ^ 1) _) = coordinateDehom j H
  rw [homogeneousChartDehom_mk]
  simp [coordinateDehom]

variable {X : Scheme.{u}} (i : X ⟶ projectiveSpace k (n + 1)) [IsClosedImmersion i]
  (p : Spec (CommRingCat.of k) ⟶ projectiveSpace k (n + 1))
  (hp : p ≫ projectiveSpaceStructure k (n + 1) = 𝟙 _)
  (s : Spec (CommRingCat.of k) ⟶ X)
  (hs : (s ≫ i) ≫ projectiveSpaceStructure k (n + 1) = 𝟙 _)
  (hdim : topologicalKrullDim X ≤ n)
  (hx : s (⊥ : PrimeSpectrum k) ∈ (i ≫ projectiveSpaceStructure k (n + 1)).smoothLocus)

/-- Original geometric data and actual original centre-open membership internally produce an actual remaining projection chart, the actual source chart prime representing the SAME original source point, and genuine derivative nonmembership in that actual prime. No source-chart point, residue-value, normalization or derivative-unit certificate is supplied. -/
theorem exists_actual_projection_chart_prime_derivative
    (hout : pointImage k n p ∉ Set.range i)
    (hc : pointImage k n p ∈ originalTangentOpen k n i s hs hdim hx) :
    ∃ (j : Fin (n + 1))
      (Q : PrimeSpectrum Γ(X,
        (i ≫ (coordinateAutomorphism k n (pointVector k n p hp) (pointVector_ne_zero k n p hp)).hom) ⁻¹ᵁ
          nativeCoordinateOpen j.succ)),
      projectionCoordinatePointVector k n (s ≫ i) p hs hp j.succ ≠ 0 ∧
      (tangentSourceChart_isAffine k n
        (i ≫ (coordinateAutomorphism k n (pointVector k n p hp) (pointVector_ne_zero k n p hp)).hom) j.succ).fromSpec Q =
          s (⊥ : PrimeSpectrum k) ∧
      tangentChartPolynomialMap k n
        (i ≫ (coordinateAutomorphism k n (pointVector k n p hp) (pointVector_ne_zero k n p hp)).hom) j.succ
        (MvPolynomial.pderiv (⟨0, Ne.symm (Fin.succ_ne_zero j)⟩ : ChartIndex j.succ)
          (coordinateDehom j.succ (projectionCoordinateTangentEquation k n p hp i s hs hdim hx))) ∉ Q.asIdeal := by
  obtain ⟨j, hw⟩ := exists_projectionCoordinatePointVector_remaining_ne_zero k n p hp i s hs hout
  let i' := i ≫ (coordinateAutomorphism k n (pointVector k n p hp) (pointVector_ne_zero k n p hp)).hom
  let w := projectionCoordinatePointVector k n (s ≫ i) p hs hp
  let K := projectionCoordinateTangentEquation k n p hp i s hs hdim hx
  have hK := projectionCoordinateTangentEquation_isHomogeneous k n p hp i s hs hdim hx
  have hder := projectionCoordinateTangentEquation_pderiv_zero_ne_zero k n p hp i s hs hdim hx hc
  have hpoint : i' (s (⊥ : PrimeSpectrum k)) = vectorPoint k n w
      (projectionCoordinatePointVector_ne_zero k n (s ≫ i) p hs hp) :=
    coordinateAutomorphism_apply_originalPoint k n (s ≫ i) p hs hp
  have hxChart : i' (s (⊥ : PrimeSpectrum k)) ∈ nativeCoordinateOpen j.succ := by
    rw [hpoint]
    change MvPolynomial.X j.succ ∉ (vectorPoint k n w _).asHomogeneousIdeal
    intro hz
    have he := (vectorPoint_mem_homogeneous k n w _ (MvPolynomial.isHomogeneous_X k j.succ)).mp hz
    exact hw (by simpa only [MvPolynomial.eval_X] using he)
  let hU := tangentSourceChart_isAffine k n i' j.succ
  have hrange : s (⊥ : PrimeSpectrum k) ∈ Set.range hU.fromSpec := by
    rw [hU.range_fromSpec]
    exact hxChart
  obtain ⟨Q, hQ⟩ := hrange
  have hgp : i' (s (⊥ : PrimeSpectrum k)) ∈
      Proj.basicOpen (ProjectiveGrading k (n + 1)) (MvPolynomial.X j.succ * MvPolynomial.pderiv 0 K) := by
    rw [hpoint]
    change MvPolynomial.X j.succ * MvPolynomial.pderiv 0 K ∉ (vectorPoint k n w _).asHomogeneousIdeal
    intro hz
    have he := (vectorPoint_mem_homogeneous k n w _
      ((MvPolynomial.isHomogeneous_X k j.succ).mul hK.pderiv)).mp hz
    exact (mul_ne_zero hw hder) (by simpa only [map_mul, MvPolynomial.eval_X] using he)
  have hchartpoint : Segre.coordinateChartInclusion (R := k) j.succ
      (Spec.map (CommRingCat.ofHom (tangentChartPolynomialMap k n i' j.succ)) Q) =
        i' (s (⊥ : PrimeSpectrum k)) := by
    have hh := congrArg (fun f => f Q) (tangentChartPolynomialMap_spec k n i' j.succ)
    change Segre.coordinateChartInclusion (R := k) j.succ
      (Spec.map (CommRingCat.ofHom (tangentChartPolynomialMap k n i' j.succ)) Q) =
        i' (hU.fromSpec Q) at hh
    rw [hQ] at hh
    exact hh
  have hmem : Spec.map (CommRingCat.ofHom (tangentChartPolynomialMap k n i' j.succ)) Q ∈
      Segre.coordinateChartInclusion (R := k) j.succ ⁻¹ᵁ
        Proj.basicOpen (ProjectiveGrading k (n + 1)) (MvPolynomial.X j.succ * MvPolynomial.pderiv 0 K) := by
    change Segre.coordinateChartInclusion (R := k) j.succ
      (Spec.map (CommRingCat.ofHom (tangentChartPolynomialMap k n i' j.succ)) Q) ∈
        Proj.basicOpen (ProjectiveGrading k (n + 1)) (MvPolynomial.X j.succ * MvPolynomial.pderiv 0 K)
    rw [hchartpoint]
    exact hgp
  rw [coordinateChartInclusion_preimage_mul_equation k n j.succ hK.pderiv] at hmem
  change tangentChartPolynomialMap k n i' j.succ (coordinateDehom j.succ (MvPolynomial.pderiv 0 K)) ∉ Q.asIdeal at hmem
  exact ⟨j, Q, hw, hQ, by simpa only [original_pderiv_coordinateDehom] using hmem⟩

end Hironaka.Geometry.ProjectiveSecant
