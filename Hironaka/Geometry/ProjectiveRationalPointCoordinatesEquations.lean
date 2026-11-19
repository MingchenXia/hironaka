import Hironaka.Geometry.ProjectiveRationalPointCoordinatesVector
import Hironaka.Geometry.ProjectiveRationalPointCoordinatesEvaluation

/-!
# The internally constructed vector represents the exact original rational scheme point

The homogeneous-fraction membership argument is adapted in arbitrary fields
from BingWangEntropy/PolynomialProjectiveAnalyticCompactness.lean, SHA256
1b87db67e837df81871282560ccf53942484fc66ca5739b2b487b9ebc2a9b861.
The native chart lift and coefficient compatibility are internally produced.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousLocalization

namespace Hironaka.Geometry.ProjectiveRationalPointCoordinates

open ProjectiveIdeal ProjectiveProjectionCenter

universe u

attribute [local instance] MvPolynomial.gradedAlgebra homogeneousChartAlgebra

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (k : Type u) [Field k] (n : ℕ)
  (p : Spec (CommRingCat.of k) ⟶ projectiveSpace k (n + 1))
  (hp : p ≫ projectiveSpaceStructure k (n + 1) = 𝟙 _)

/-- The native basic-open localization element evaluates at the original internally recovered vector. -/
theorem homogeneousChartPoint_isLocalizationElem {d : ℕ}
    {F : MvPolynomial (Fin (n + 2)) k} (hF : F.IsHomogeneous d) :
    homogeneousChartPoint k n p hp
      (Away.isLocalizationElem (MvPolynomial.isHomogeneous_X k (chosenChart k n p)) hF) =
      MvPolynomial.eval (pointVector k n p hp) F := by
  have helem : Away.isLocalizationElem (MvPolynomial.isHomogeneous_X k (chosenChart k n p)) hF =
      Away.mk (ProjectiveGrading k (n + 1)) (MvPolynomial.isHomogeneous_X k (chosenChart k n p))
        d F (by simpa using hF) := by
    apply HomogeneousLocalization.val_injective
    simp only [Away.isLocalizationElem, Away.val_mk, pow_one]
  rw [helem, homogeneousChartPoint_mk]

/-- Original positive-degree homogeneous equations at the original image point are the actual vector equations. -/
theorem pointImage_mem_homogeneous_positive {d : ℕ} (hd : 0 < d)
    {F : MvPolynomial (Fin (n + 2)) k} (hF : F.IsHomogeneous d) :
    F ∈ (pointImage k n p).asHomogeneousIdeal ↔ MvPolynomial.eval (pointVector k n p hp) F = 0 := by
  let G := ProjectiveGrading k (n + 1)
  let j := chosenChart k n p
  let e := homogeneousChartPoint k n p hp
  have himage : pointImage k n p =
      Proj.awayι G (X j) (MvPolynomial.isHomogeneous_X k j) (by decide : 0 < (1 : ℕ))
        (Spec.map (CommRingCat.ofHom e.toRingHom) (⊥ : PrimeSpectrum k)) :=
    congrArg (fun q : Spec (CommRingCat.of k) ⟶ projectiveSpace k (n + 1) => q (⊥ : PrimeSpectrum k))
      (homogeneousChartPoint_spec k n p hp)
  have hk : (Spec.map (CommRingCat.ofHom e.toRingHom) (⊥ : PrimeSpectrum k)).asIdeal =
      RingHom.ker e.toRingHom := rfl
  have hopen : pointImage k n p ∈ Proj.basicOpen G F ↔
      e (Away.isLocalizationElem (MvPolynomial.isHomogeneous_X k j) hF) ≠ 0 := by
    rw [himage]
    change (Spec.map (CommRingCat.ofHom e.toRingHom) (⊥ : PrimeSpectrum k)) ∈
      Proj.awayι G (X j) (MvPolynomial.isHomogeneous_X k j) (by decide : 0 < (1 : ℕ)) ⁻¹ᵁ
        Proj.basicOpen G F ↔ _
    rw [Proj.awayι_preimage_basicOpen G (MvPolynomial.isHomogeneous_X k j) (by decide) hF hd]
    rw [PrimeSpectrum.mem_basicOpen, hk]
    rfl
  have hzero : e (Away.isLocalizationElem (MvPolynomial.isHomogeneous_X k j) hF) = 0 ↔
      MvPolynomial.eval (pointVector k n p hp) F = 0 := by
    change homogeneousChartPoint k n p hp _ = 0 ↔ _
    rw [homogeneousChartPoint_isLocalizationElem]
  change F ∉ (pointImage k n p).asHomogeneousIdeal ↔ _ at hopen
  simpa only [not_not] using
    (not_congr hopen).trans (by simpa only [not_not] using hzero)

/-- Every original homogeneous equation, including degree zero, has its exact actual vector readback. -/
theorem pointImage_mem_homogeneous {d : ℕ} {F : MvPolynomial (Fin (n + 2)) k}
    (hF : F.IsHomogeneous d) :
    F ∈ (pointImage k n p).asHomogeneousIdeal ↔ MvPolynomial.eval (pointVector k n p hp) F = 0 := by
  cases d with
  | succ d => exact pointImage_mem_homogeneous_positive k n p hp (Nat.succ_pos _) hF
  | zero =>
    let j := chosenChart k n p
    let x := pointImage k n p
    have hX : X j ∉ x.asHomogeneousIdeal := by
      rw [pointImage_mem_homogeneous_positive k n p hp (by decide : 0 < (1 : ℕ))
        (MvPolynomial.isHomogeneous_X k j), MvPolynomial.eval_X]
      change pointVector k n p hp (chosenChart k n p) ≠ 0
      rw [pointVector_chosenChart]
      exact one_ne_zero
    have hprod : (F * X j).IsHomogeneous 1 := by
      simpa using hF.mul (MvPolynomial.isHomogeneous_X k j)
    have hmem : F ∈ x.asHomogeneousIdeal ↔ F * X j ∈ x.asHomogeneousIdeal :=
      ⟨fun h => Ideal.mul_mem_right _ _ h,
        fun h => (x.isPrime.mem_or_mem h).resolve_right hX⟩
    rw [hmem, pointImage_mem_homogeneous_positive k n p hp (by decide : 0 < (1 : ℕ)) hprod,
      map_mul, MvPolynomial.eval_X]
    rw [show pointVector k n p hp j = 1 from pointVector_chosenChart k n p hp, mul_one]

/-- The internally recovered vector has exactly the original rational morphism's image point. -/
theorem pointVector_image : vectorPoint k n (pointVector k n p hp) (pointVector_ne_zero k n p hp) =
    pointImage k n p := by
  apply ProjectiveSpectrum.ext
  apply HomogeneousIdeal.ext'
  intro d F hF
  exact (vectorPoint_mem_homogeneous k n _ _ hF).trans (pointImage_mem_homogeneous k n p hp hF).symm

include hp in
/-- The original rational scheme point internally produces genuine original homogeneous coordinates. -/
theorem exists_vector_representation : ∃ (v : Fin (n + 2) → k) (hv : v ≠ 0),
    vectorPoint k n v hv = pointImage k n p :=
  ⟨pointVector k n p hp, pointVector_ne_zero k n p hp, pointVector_image k n p hp⟩

end Hironaka.Geometry.ProjectiveRationalPointCoordinates
