import DeJongAlterations.Geometry.SegreGluing
import DeJongAlterations.Geometry.SegreGluingCoordinates
import Mathlib.AlgebraicGeometry.Gluing

/-!
# The native Segre closed immersion

The morphism is glued from the actual affine Segre chart maps. Compatibility
comes from the actual projective product pullback equation and the native
coordinate overlap producer, without supplied compatibility certificates.
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

variable {R : Type u} [CommRing R] {m n : ℕ} {X : Scheme.{u}}

/-- The actual left affine tensor-chart projection. -/
def tensorChartLeft (i : Fin (m + 1)) (j : Fin (n + 1)) :
    Spec (CommRingCat.of (CoordinateRing R i ⊗[R] CoordinateRing R j)) ⟶
      Spec (CommRingCat.of (CoordinateRing R i)) :=
  Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom :
    CoordinateRing R i →+* CoordinateRing R i ⊗[R] CoordinateRing R j))

/-- The actual right affine tensor-chart projection. -/
def tensorChartRight (i : Fin (m + 1)) (j : Fin (n + 1)) :
    Spec (CommRingCat.of (CoordinateRing R i ⊗[R] CoordinateRing R j)) ⟶
      Spec (CommRingCat.of (CoordinateRing R j)) :=
  Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight.toRingHom :
    CoordinateRing R j →+* CoordinateRing R i ⊗[R] CoordinateRing R j))

/-- The actual affine Segre chart map to the target polynomial coordinate spectrum. -/
def affineChartMap (i : Fin (m + 1)) (j : Fin (n + 1)) :
    Spec (CommRingCat.of (CoordinateRing R i ⊗[R] CoordinateRing R j)) ⟶
      Spec (CommRingCat.of (CoordinateRing R (indexEquiv m n (i, j)))) :=
  Spec.map (CommRingCat.ofHom (chartMap (R := R) i j).toRingHom)

/-- Actual pulled-back Segre coordinates multiply the actual coordinates of the two factors. -/
theorem pullRingHom_affineChartMap_coordinate
    (i k : Fin (m + 1)) (j l : Fin (n + 1))
    (f : X ⟶ Spec (CommRingCat.of (CoordinateRing R i ⊗[R] CoordinateRing R j))) :
    pullRingHom (f ≫ affineChartMap i j)
        (coordinateDehomCoord (indexEquiv m n (i, j)) (indexEquiv m n (k, l))) =
      pullRingHom (f ≫ tensorChartLeft i j) (coordinateDehomCoord i k) *
        pullRingHom (f ≫ tensorChartRight i j) (coordinateDehomCoord j l) := by
  simp only [affineChartMap, tensorChartLeft, tensorChartRight, pullRingHom_comp,
    RingHom.comp_apply]
  change pullRingHom f (chartMap i j
      (coordinateDehomCoord (indexEquiv m n (i, j)) (indexEquiv m n (k, l)))) =
    pullRingHom f (Algebra.TensorProduct.includeLeftRingHom (coordinateDehomCoord i k)) *
      pullRingHom f (Algebra.TensorProduct.includeRight (coordinateDehomCoord j l))
  rw [chartMap_coordinate, ← map_mul]
  congr 1
  simp [chartCoordinate, Algebra.TensorProduct.includeLeftRingHom,
    Algebra.TensorProduct.tmul_mul_tmul]

/-- The actual Segre chart coefficient map is the original left-factor coefficient map. -/
theorem pullRingHom_affineChartMap_coefficient
    (i : Fin (m + 1)) (j : Fin (n + 1))
    (f : X ⟶ Spec (CommRingCat.of (CoordinateRing R i ⊗[R] CoordinateRing R j)))
    (r : R) :
    pullRingHom (f ≫ affineChartMap i j) (MvPolynomial.C r) =
      pullRingHom (f ≫ tensorChartLeft i j) (MvPolynomial.C r) := by
  simp only [affineChartMap, tensorChartLeft, pullRingHom_comp, RingHom.comp_apply]
  change pullRingHom f (chartMap i j (algebraMap R
      (CoordinateRing R (indexEquiv m n (i, j))) r)) =
    pullRingHom f (Algebra.TensorProduct.includeLeftRingHom
      (algebraMap R (CoordinateRing R i) r))
  rw [(chartMap (R := R) i j).commutes]
  rfl

/-- The actual local Segre morphisms agree on their native source-chart pullback. -/
theorem chartToProjective_compatibility
    (i k : Fin (m + 1)) (j l : Fin (n + 1)) :
    pullback.fst (productChartInclusion (R := R) i j) (productChartInclusion k l) ≫
        chartToProjective i j =
      pullback.snd (productChartInclusion (R := R) i j) (productChartInclusion k l) ≫
        chartToProjective k l := by
  let f := pullback.fst (productChartInclusion (R := R) i j) (productChartInclusion k l)
  let g := pullback.snd (productChartInclusion (R := R) i j) (productChartInclusion k l)
  have hleft : (f ≫ tensorChartLeft i j) ≫ coordinateChartInclusion i =
      (g ≫ tensorChartLeft k l) ≫ coordinateChartInclusion k := by
    have h := congrArg
      (fun t => t ≫ pullback.fst (projectiveSpaceStructure R m) (projectiveSpaceStructure R n))
      (pullback.condition (f := productChartInclusion (R := R) i j)
        (g := productChartInclusion k l))
    simpa only [Category.assoc, productChartInclusion_fst, tensorChartLeft] using h
  have hright : (f ≫ tensorChartRight i j) ≫ coordinateChartInclusion j =
      (g ≫ tensorChartRight k l) ≫ coordinateChartInclusion l := by
    have h := congrArg
      (fun t => t ≫ pullback.snd (projectiveSpaceStructure R m) (projectiveSpaceStructure R n))
      (pullback.condition (f := productChartInclusion (R := R) i j)
        (g := productChartInclusion k l))
    simpa only [Category.assoc, productChartInclusion_snd, tensorChartRight] using h
  obtain ⟨hlu, hlcoeff, hlcross⟩ :=
    coordinateChart_transition i k (f ≫ tensorChartLeft i j) (g ≫ tensorChartLeft k l) hleft
  obtain ⟨hru, _hrcoeff, hrcross⟩ :=
    coordinateChart_transition j l (f ≫ tensorChartRight i j) (g ≫ tensorChartRight k l) hright
  have hu : IsUnit (pullRingHom (f ≫ affineChartMap i j)
      (coordinateDehomCoord (indexEquiv m n (i, j)) (indexEquiv m n (k, l)))) := by
    rw [pullRingHom_affineChartMap_coordinate]
    exact hlu.mul hru
  have hcoeff : ∀ r : R, pullRingHom (f ≫ affineChartMap i j) (MvPolynomial.C r) =
      pullRingHom (g ≫ affineChartMap k l) (MvPolynomial.C r) := by
    intro r
    rw [pullRingHom_affineChartMap_coefficient, pullRingHom_affineChartMap_coefficient]
    exact hlcoeff r
  have hcross : ∀ z, pullRingHom (f ≫ affineChartMap i j)
        (coordinateDehomCoord (indexEquiv m n (i, j)) z) =
      pullRingHom (g ≫ affineChartMap k l)
          (coordinateDehomCoord (indexEquiv m n (k, l)) z) *
        pullRingHom (f ≫ affineChartMap i j)
          (coordinateDehomCoord (indexEquiv m n (i, j)) (indexEquiv m n (k, l))) := by
    intro z
    obtain ⟨⟨a, b⟩, rfl⟩ := (indexEquiv m n).surjective z
    rw [pullRingHom_affineChartMap_coordinate i a j b f,
      pullRingHom_affineChartMap_coordinate k a l b g,
      pullRingHom_affineChartMap_coordinate i k j l f]
    rw [hlcross a, hrcross b]
    ring
  simpa only [Category.assoc, affineChartMap, chartToProjective] using
    coordinateChartComparison_of_globalSections (indexEquiv m n (i, j))
      (indexEquiv m n (k, l)) (f ≫ affineChartMap i j) (g ≫ affineChartMap k l)
      hu hcoeff hcross

/-- The actual native Segre morphism, glued from the actual affine coordinate maps. -/
def segre (R : Type u) [CommRing R] (m n : ℕ) :
    projectiveProduct R m n ⟶ projectiveSpace R (dimension m n) :=
  (productCoordinateCover R m n).glueMorphisms
    (fun ij => chartToProjective ij.1 ij.2)
    (fun ij kl => chartToProjective_compatibility ij.1 kl.1 ij.2 kl.2)

/-- The glued Segre morphism has the actual prescribed map on every source tensor chart. -/
@[reassoc (attr := simp)]
theorem productChartInclusion_segre (i : Fin (m + 1)) (j : Fin (n + 1)) :
    productChartInclusion (R := R) i j ≫ segre R m n = chartToProjective i j :=
  (productCoordinateCover R m n).ι_glueMorphisms _ _ (i, j)

/-- The actual Segre map preserves the original common coefficient-ring structure map. -/
theorem segre_structure :
    segre R m n ≫ projectiveSpaceStructure R (dimension m n) =
      pullback.fst (projectiveSpaceStructure R m) (projectiveSpaceStructure R n) ≫
        projectiveSpaceStructure R m := by
  apply (productCoordinateCover R m n).hom_ext
  rintro ⟨i, j⟩
  change productChartInclusion i j ≫ segre R m n ≫ _ =
    productChartInclusion i j ≫ _ ≫ _
  rw [productChartInclusion_segre_assoc, chartToProjective_structure,
    productChartInclusion_structure]

/-- The full inverse image of every native target coordinate chart is exactly its actual source product chart. -/
theorem segre_preimage_coordinate (k : Fin (m + 1)) (l : Fin (n + 1)) :
    segre R m n ⁻¹ᵁ Proj.basicOpen (projectiveSpaceGrading R (dimension m n))
        (MvPolynomial.X (indexEquiv m n (k, l))) =
      productCoordinateOpen k l := by
  ext x
  obtain ⟨⟨i, j⟩, y, rfl⟩ := (productCoordinateCover R m n).exists_eq x
  change y ∈ (productChartInclusion i j ≫ segre R m n) ⁻¹ᵁ
      Proj.basicOpen (projectiveSpaceGrading R (dimension m n))
        (MvPolynomial.X (indexEquiv m n (k, l))) ↔
    y ∈ productChartInclusion i j ⁻¹ᵁ productCoordinateOpen k l
  rw [productChartInclusion_segre, chartToProjective_preimage_coordinate,
    productChartInclusion_preimage_coordinate]

/-- The actual local surjective affine chart map is a native Cartesian chart of the global Segre map. -/
theorem segre_chart_isPullback (i : Fin (m + 1)) (j : Fin (n + 1)) :
    IsPullback (affineChartMap (R := R) i j) (productChartInclusion i j)
      (coordinateChartInclusion (indexEquiv m n (i, j))) (segre R m n) := by
  apply IsOpenImmersion.isPullback
  · exact productChartInclusion_segre i j
  · rw [coordinateChartInclusion_opensRange, segre_preimage_coordinate,
      productChartInclusion_opensRange]

/-- The actual native Segre morphism is a closed immersion over every commutative coefficient ring. -/
instance segre_isClosedImmersion : IsClosedImmersion (segre R m n) := by
  apply IsZariskiLocalAtTarget.of_openCover (coordinateCover R (dimension m n))
  intro z
  obtain ⟨⟨i, j⟩, rfl⟩ := (indexEquiv m n).surjective z
  change IsClosedImmersion (pullback.snd (segre R m n)
    (coordinateChartInclusion (indexEquiv m n (i, j))))
  let h := (segre_chart_isPullback (R := R) i j).flip
  rw [← h.isoPullback_inv_snd]
  apply (MorphismProperty.cancel_left_of_respectsIso
    (P := @IsClosedImmersion) h.isoPullback.inv _).mpr
  exact IsClosedImmersion.spec_of_surjective _ (chartMap_surjective i j)

end DeJongAlterations.Geometry.Segre
