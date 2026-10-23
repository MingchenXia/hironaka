import DeJongAlterations.Geometry.SegreChart
import DeJongAlterations.Geometry.ProjectiveIdealCoordinateIdeal

/-!
# Actual source charts for the global Segre construction

The native projective product has an actual open cover by the tensor spectra
used in the released Segre chart construction. No covering or product
identification is assumed.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial TopologicalSpace
open scoped TensorProduct
open DeJongAlterations.Geometry.ProjectiveIdeal
open DeJongAlterations.Algebra.Segre

noncomputable section

namespace DeJongAlterations.Geometry.Segre

universe u

attribute [local instance] MvPolynomial.gradedAlgebra homogeneousChartAlgebra

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {R : Type u} [CommRing R] {m n d : ℕ}

/-- The actual native fiber product of the two projective spaces. -/
def projectiveProduct (R : Type u) [CommRing R] (m n : ℕ) : Scheme :=
  pullback (projectiveSpaceStructure R m) (projectiveSpaceStructure R n)

/-- The actual polynomial coordinate chart immersion has its native basic-open range. -/
theorem coordinateChartInclusion_opensRange (i : Fin (d + 1)) :
    (coordinateChartInclusion (R := R) i).opensRange =
      Proj.basicOpen (projectiveSpaceGrading R d) (MvPolynomial.X i) := by
  unfold coordinateChartInclusion
  rw [Scheme.Hom.opensRange_comp_of_isIso, Scheme.Opens.opensRange_ι]

/-- The actual affine polynomial spectra form an open cover of native projective space. -/
@[simps! I₀ X f]
def coordinateCover (R : Type u) [CommRing R] (d : ℕ) :
    (projectiveSpace R d).OpenCover :=
  Scheme.Cover.mkOfCovers (Fin (d + 1))
    (fun i => Spec (CommRingCat.of (CoordinateRing R i)))
    (fun i => coordinateChartInclusion i)
    (by
      intro x
      have hx : x ∈ (⊤ : (projectiveSpace R d).Opens) := trivial
      rw [← iSup_nativeCoordinateOpen_eq_top (R := R) (n := d)] at hx
      obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
      change x ∈ Proj.basicOpen (projectiveSpaceGrading R d) (MvPolynomial.X i) at hi
      rw [← coordinateChartInclusion_opensRange] at hi
      exact ⟨i, hi⟩)

/-- The actual affine tensor spectrum is the fiber product of the two chart structure maps. -/
theorem productChart_isPullback (i : Fin (m + 1)) (j : Fin (n + 1)) :
    IsPullback
      (Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeLeftRingHom :
          CoordinateRing R i →+* CoordinateRing R i ⊗[R] CoordinateRing R j)))
      (Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight.toRingHom :
          CoordinateRing R j →+* CoordinateRing R i ⊗[R] CoordinateRing R j)))
      (coordinateChartInclusion i ≫ projectiveSpaceStructure R m)
      (coordinateChartInclusion j ≫ projectiveSpaceStructure R n) := by
  simpa only [coordinateChartInclusion_structure] using chartProduct_isPullback (R := R) i j

/-- The canonical actual tensor-spectrum identification, derived from its native universal property. -/
def productChartIso (i : Fin (m + 1)) (j : Fin (n + 1)) :
    Spec (CommRingCat.of (CoordinateRing R i ⊗[R] CoordinateRing R j)) ≅
      pullback (coordinateChartInclusion i ≫ projectiveSpaceStructure R m)
        (coordinateChartInclusion j ≫ projectiveSpaceStructure R n) :=
  (productChart_isPullback (R := R) i j).isoPullback

/-- The actual inclusion of a tensor coordinate chart into the native projective product. -/
def productChartInclusion (i : Fin (m + 1)) (j : Fin (n + 1)) :
    Spec (CommRingCat.of (CoordinateRing R i ⊗[R] CoordinateRing R j)) ⟶
      projectiveProduct R m n :=
  (productChartIso i j).hom ≫
    (AlgebraicGeometry.Scheme.Pullback.openCoverOfLeftRight
      (coordinateCover R m) (coordinateCover R n)
      (projectiveSpaceStructure R m) (projectiveSpaceStructure R n)).f (i, j)

instance productChartInclusion_isOpenImmersion (i : Fin (m + 1)) (j : Fin (n + 1)) :
    IsOpenImmersion (productChartInclusion (R := R) i j) := by
  unfold productChartInclusion
  infer_instance

/-- Both source coordinate covers produce the actual tensor-spectrum cover of the projective product. -/
@[simps! I₀ X f]
def productCoordinateCover (R : Type u) [CommRing R] (m n : ℕ) :
    (projectiveProduct R m n).OpenCover :=
  (AlgebraicGeometry.Scheme.Pullback.openCoverOfLeftRight
    (coordinateCover R m) (coordinateCover R n)
    (projectiveSpaceStructure R m) (projectiveSpaceStructure R n)).copy
    (Fin (m + 1) × Fin (n + 1))
    (fun ij => Spec (CommRingCat.of (CoordinateRing R ij.1 ⊗[R] CoordinateRing R ij.2)))
    (fun ij => productChartInclusion ij.1 ij.2)
    (Equiv.refl _)
    (fun ij => productChartIso ij.1 ij.2)
    (fun _ => rfl)

@[reassoc (attr := simp)]
theorem productChartInclusion_fst (i : Fin (m + 1)) (j : Fin (n + 1)) :
    productChartInclusion (R := R) i j ≫
        pullback.fst (projectiveSpaceStructure R m) (projectiveSpaceStructure R n) =
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeLeftRingHom :
          CoordinateRing R i →+* CoordinateRing R i ⊗[R] CoordinateRing R j)) ≫
        coordinateChartInclusion i := by
  simp only [productChartInclusion, Category.assoc,
    AlgebraicGeometry.Scheme.Pullback.openCoverOfLeftRight_f, pullback.map,
    pullback.lift_fst]
  exact (productChart_isPullback (R := R) i j).isoPullback_hom_fst_assoc _

@[reassoc (attr := simp)]
theorem productChartInclusion_snd (i : Fin (m + 1)) (j : Fin (n + 1)) :
    productChartInclusion (R := R) i j ≫
        pullback.snd (projectiveSpaceStructure R m) (projectiveSpaceStructure R n) =
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight.toRingHom :
          CoordinateRing R j →+* CoordinateRing R i ⊗[R] CoordinateRing R j)) ≫
        coordinateChartInclusion j := by
  simp only [productChartInclusion, Category.assoc,
    AlgebraicGeometry.Scheme.Pullback.openCoverOfLeftRight_f, pullback.map,
    pullback.lift_snd]
  exact (productChart_isPullback (R := R) i j).isoPullback_hom_snd_assoc _

/-- The product-chart structure triangle is the actual coefficient-ring triangle. -/
theorem productChartInclusion_structure (i : Fin (m + 1)) (j : Fin (n + 1)) :
    productChartInclusion (R := R) i j ≫
        pullback.fst (projectiveSpaceStructure R m) (projectiveSpaceStructure R n) ≫
          projectiveSpaceStructure R m =
      Spec.map (CommRingCat.ofHom
        (algebraMap R (CoordinateRing R i ⊗[R] CoordinateRing R j))) := by
  rw [productChartInclusion_fst_assoc, coordinateChartInclusion_structure, ← Spec.map_comp]
  rfl

/-- Pulling a native coordinate open back to an actual affine chart gives the true coordinate basic open. -/
theorem coordinateChartInclusion_preimage_coordinate (i k : Fin (d + 1)) :
    coordinateChartInclusion (R := R) i ⁻¹ᵁ
        Proj.basicOpen (projectiveSpaceGrading R d) (MvPolynomial.X k) =
      PrimeSpectrum.basicOpen (coordinateDehomCoord (R := R) i k) := by
  rw [coordinateChartInclusion_eq, Scheme.Hom.comp_preimage,
    Proj.awayι_preimage_basicOpen (𝒜 := projectiveSpaceGrading R d)
      (MvPolynomial.isHomogeneous_X R i) (by decide : 0 < (1 : ℕ))
      (MvPolynomial.isHomogeneous_X R k) (by decide : 0 < (1 : ℕ)),
    SpecMap_preimage_basicOpen]
  congr 1
  change homogeneousChartDehom i
    (HomogeneousLocalization.Away.mk (ProjectiveGrading R d)
      (MvPolynomial.isHomogeneous_X R i) 1 ((MvPolynomial.X k) ^ 1) _) = _
  rw [homogeneousChartDehom_mk]
  simp [coordinateDehom]

/-- Every target coordinate inverse image on a genuine Segre chart is the actual product-coordinate basic open. -/
theorem chartToProjective_preimage_coordinate
    (i k : Fin (m + 1)) (j l : Fin (n + 1)) :
    chartToProjective (R := R) i j ⁻¹ᵁ
        Proj.basicOpen (projectiveSpaceGrading R (dimension m n))
          (MvPolynomial.X (indexEquiv m n (k, l))) =
      PrimeSpectrum.basicOpen (chartCoordinate (R := R) i j k l) := by
  rw [chartToProjective, Scheme.Hom.comp_preimage,
    coordinateChartInclusion_preimage_coordinate, SpecMap_preimage_basicOpen]
  congr 1
  exact chartMap_coordinate i j k l

/-- The actual product coordinate open: both factor coordinates must be nonzero. -/
def productCoordinateOpen (i : Fin (m + 1)) (j : Fin (n + 1)) :
    (projectiveProduct R m n).Opens :=
  pullback.fst (projectiveSpaceStructure R m) (projectiveSpaceStructure R n) ⁻¹ᵁ
      Proj.basicOpen (projectiveSpaceGrading R m) (MvPolynomial.X i) ⊓
    pullback.snd (projectiveSpaceStructure R m) (projectiveSpaceStructure R n) ⁻¹ᵁ
      Proj.basicOpen (projectiveSpaceGrading R n) (MvPolynomial.X j)

/-- On every actual tensor chart, the product-open condition is the product-coordinate basic open. -/
theorem productChartInclusion_preimage_coordinate
    (i k : Fin (m + 1)) (j l : Fin (n + 1)) :
    productChartInclusion (R := R) i j ⁻¹ᵁ productCoordinateOpen k l =
      PrimeSpectrum.basicOpen (chartCoordinate (R := R) i j k l) := by
  unfold productCoordinateOpen
  rw [Scheme.Hom.preimage_inf, ← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage,
    productChartInclusion_fst, productChartInclusion_snd,
    Scheme.Hom.comp_preimage, Scheme.Hom.comp_preimage,
    coordinateChartInclusion_preimage_coordinate, coordinateChartInclusion_preimage_coordinate,
    SpecMap_preimage_basicOpen, SpecMap_preimage_basicOpen, ← PrimeSpectrum.basicOpen_mul]
  congr 1
  simp [chartCoordinate, Algebra.TensorProduct.includeLeftRingHom,
    Algebra.TensorProduct.tmul_mul_tmul]

/-- The tensor chart has exactly the expected whole product-open range. -/
theorem productChartInclusion_opensRange (i : Fin (m + 1)) (j : Fin (n + 1)) :
    (productChartInclusion (R := R) i j).opensRange = productCoordinateOpen i j := by
  apply le_antisymm
  · rintro x ⟨y, rfl⟩
    have h := congrArg (fun U : (Spec (CommRingCat.of
        (CoordinateRing R i ⊗[R] CoordinateRing R j))).Opens => y ∈ U)
      (productChartInclusion_preimage_coordinate (R := R) i i j j)
    exact h.mpr (by simp [chartCoordinate, ← Algebra.TensorProduct.one_def])
  · let V := productCoordinateOpen (R := R) i j
    let p := pullback.fst (projectiveSpaceStructure R m) (projectiveSpaceStructure R n)
    let q := pullback.snd (projectiveSpaceStructure R m) (projectiveSpaceStructure R n)
    have hl : Set.range (V.ι ≫ p) ⊆ Set.range (coordinateChartInclusion (R := R) i) := by
      rintro _ ⟨y, rfl⟩
      change p (V.ι y) ∈ (coordinateChartInclusion (R := R) i).opensRange
      rw [coordinateChartInclusion_opensRange]
      exact y.property.1
    have hr : Set.range (V.ι ≫ q) ⊆ Set.range (coordinateChartInclusion (R := R) j) := by
      rintro _ ⟨y, rfl⟩
      change q (V.ι y) ∈ (coordinateChartInclusion (R := R) j).opensRange
      rw [coordinateChartInclusion_opensRange]
      exact y.property.2
    let l := IsOpenImmersion.lift (coordinateChartInclusion (R := R) i) (V.ι ≫ p) hl
    let r := IsOpenImmersion.lift (coordinateChartInclusion (R := R) j) (V.ι ≫ q) hr
    have hw : l ≫ (coordinateChartInclusion i ≫ projectiveSpaceStructure R m) =
        r ≫ (coordinateChartInclusion j ≫ projectiveSpaceStructure R n) := by
      simp only [l, r, ← Category.assoc, IsOpenImmersion.lift_fac]
      exact congrArg (fun f => V.ι ≫ f) pullback.condition
    let t := (productChart_isPullback (R := R) i j).lift l r hw
    have ht : t ≫ productChartInclusion i j = V.ι := by
      apply pullback.hom_ext
      · rw [Category.assoc, productChartInclusion_fst, ← Category.assoc]
        change ((productChart_isPullback (R := R) i j).lift l r hw ≫ _) ≫ _ = _
        rw [IsPullback.lift_fst]
        exact IsOpenImmersion.lift_fac _ _ _
      · rw [Category.assoc, productChartInclusion_snd, ← Category.assoc]
        change ((productChart_isPullback (R := R) i j).lift l r hw ≫ _) ≫ _ = _
        rw [IsPullback.lift_snd]
        exact IsOpenImmersion.lift_fac _ _ _
    intro x hx
    refine ⟨t ⟨x, hx⟩, ?_⟩
    change (t ≫ productChartInclusion i j) ⟨x, hx⟩ = x
    rw [ht]
    rfl

end DeJongAlterations.Geometry.Segre
