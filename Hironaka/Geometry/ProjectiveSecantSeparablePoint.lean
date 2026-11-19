import Hironaka.Algebra.ProjectiveSecantSeparablePoint
import Hironaka.Algebra.ProjectiveSecantProjectionChartDerivative
import Hironaka.Geometry.ProjectiveSecantProjectionChartPoint
import Hironaka.Geometry.BlowupProjectiveEmbeddingCoefficients

/-!
# Actual finite separable rational scheme points in original homogeneous parameter opens
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MvPolynomial

namespace Hironaka.Geometry.ProjectiveSecant

open ProjectiveIdeal ProjectiveRationalPointCoordinates BlowupProjectiveEmbedding
open Algebra.ProjectiveSecant

universe u

attribute [local instance] MvPolynomial.gradedAlgebra homogeneousChartAlgebra

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (k : Type u) [Field k] (n : ℕ)

/-- The actual whole normalized coordinate-chart algebra map internally gives an actual rational projective scheme point. -/
def rationalPointFromVector (v : Fin (n + 2) → k) (j : Fin (n + 1)) :
    Spec (CommRingCat.of k) ⟶ projectiveSpace k (n + 1) :=
  Spec.map (CommRingCat.ofHom (MvPolynomial.aeval (projectionChartVector k n v j)).toRingHom) ≫
    Segre.coordinateChartInclusion (R := k) j.succ

/-- The actual normalized scheme point retains its literal whole coefficient triangle. -/
theorem rationalPointFromVector_structure (v : Fin (n + 2) → k) (j : Fin (n + 1)) :
    rationalPointFromVector k n v j ≫ projectiveSpaceStructure k (n + 1) = 𝟙 _ := by
  let a : CoordinateRing k j.succ →ₐ[k] k := MvPolynomial.aeval (projectionChartVector k n v j)
  have hc : CommRingCat.ofHom (algebraMap k (CoordinateRing k j.succ)) ≫ CommRingCat.ofHom a.toRingHom =
      𝟙 (CommRingCat.of k) := by
    ext c
    exact a.commutes c
  rw [rationalPointFromVector, Category.assoc, Segre.coordinateChartInclusion_structure, ← Spec.map_comp]
  change Spec.map (CommRingCat.ofHom (algebraMap k (CoordinateRing k j.succ)) ≫ CommRingCat.ofHom a.toRingHom) = _
  rw [hc]
  simp

/-- Actual original nonvanishing coordinates internally put their actual normalized native scheme point in the SAME original homogeneous open. -/
theorem rationalPointFromVector_mem_basicOpen (v : Fin (n + 2) → k) (j : Fin (n + 1))
    (hj : v j.succ ≠ 0) {d : ℕ} {H : MvPolynomial (Fin (n + 2)) k}
    (hH : H.IsHomogeneous d) (hne : MvPolynomial.eval v H ≠ 0) :
    rationalPointFromVector k n v j (⊥ : PrimeSpectrum k) ∈ Proj.basicOpen (ProjectiveGrading k (n + 1)) H := by
  have hd : MvPolynomial.eval (projectionChartVector k n v j) (coordinateDehom j.succ H) ≠ 0 := by
    rw [original_eval_dehom_projectionChartVector k n v j hj]
    have he : MvPolynomial.eval (fun l => (v j.succ)⁻¹ * v l) H =
        (v j.succ)⁻¹ ^ d * MvPolynomial.eval v H :=
      homogeneous_eval₂_scaled hH (RingHom.id k) v (v j.succ)⁻¹
    rw [he]
    exact mul_ne_zero (pow_ne_zero _ (inv_ne_zero hj)) hne
  have hm : rationalPointFromVector k n v j (⊥ : PrimeSpectrum k) ∈
      Proj.basicOpen (ProjectiveGrading k (n + 1)) (MvPolynomial.X j.succ * H) := by
    let a : CoordinateRing k j.succ →ₐ[k] k := MvPolynomial.aeval (projectionChartVector k n v j)
    change Spec.map (CommRingCat.ofHom a.toRingHom)
      (⊥ : PrimeSpectrum k) ∈ Segre.coordinateChartInclusion (R := k) j.succ ⁻¹ᵁ
        Proj.basicOpen (ProjectiveGrading k (n + 1)) (MvPolynomial.X j.succ * H)
    rw [coordinateChartInclusion_preimage_mul_equation k n j.succ hH]
    change MvPolynomial.eval (projectionChartVector k n v j) (coordinateDehom j.succ H) ∉ (⊥ : Ideal k)
    simpa only [Ideal.mem_bot] using hd
  change H ∉ (rationalPointFromVector k n v j (⊥ : PrimeSpectrum k)).asHomogeneousIdeal
  intro h
  exact hm ((rationalPointFromVector k n v j (⊥ : PrimeSpectrum k)).asHomogeneousIdeal.toIdeal.mul_mem_left
    (MvPolynomial.X j.succ) h)

/-- Every original nonzero homogeneous parameter form over ANY original field internally produces an actual finite separable field and actual rational scheme point whose actual original coefficient image lies in the SAME original parameter open. Both literal whole coefficient triangles are retained; no vector or point certificate is supplied. -/
theorem exists_finite_separable_projective_point {d : ℕ}
    (F : MvPolynomial (Fin (n + 2)) k) (hF : F.IsHomogeneous d) (hne : F ≠ 0) :
    ∃ L : IntermediateField k (SeparableClosure k), FiniteDimensional k L ∧ Algebra.IsSeparable k L ∧
      ∃ q : Spec (CommRingCat.of L) ⟶ projectiveSpace L (n + 1),
        q ≫ projectiveSpaceStructure L (n + 1) = 𝟙 _ ∧
        (q ≫ projectiveCoefficientMap (algebraMap k L) (n + 1)) ≫ projectiveSpaceStructure k (n + 1) =
          Spec.map (CommRingCat.ofHom (algebraMap k L)) ∧
        (q ≫ projectiveCoefficientMap (algebraMap k L) (n + 1)) (⊥ : PrimeSpectrum L) ∈
          Proj.basicOpen (ProjectiveGrading k (n + 1)) F := by
  obtain ⟨L, hfin, hsep, v, hj, hv⟩ := exists_finite_separable_nonvanishing_with_coordinate k
    (Fin (n + 2)) (0 : Fin (n + 1)).succ F hne
  let q := rationalPointFromVector L n v 0
  have hq := rationalPointFromVector_structure L n v 0
  refine ⟨L, hfin, hsep, q, hq, ?_, ?_⟩
  · rw [Category.assoc, projectiveCoefficientMap_structure, ← Category.assoc, hq, Category.id_comp]
  · change q (⊥ : PrimeSpectrum L) ∈ Proj.basicOpen (ProjectiveGrading L (n + 1)) (MvPolynomial.map (algebraMap k L) F)
    apply rationalPointFromVector_mem_basicOpen L n v 0 hj (hF.map (algebraMap k L))
    change MvPolynomial.eval₂ (algebraMap k L) v F ≠ 0 at hv
    simpa only [MvPolynomial.eval₂_eq_eval_map] using hv

end Hironaka.Geometry.ProjectiveSecant
