import DeJongAlterations.Algebra.SegreGluing
import DeJongAlterations.Geometry.SegreChart

/-!
# Actual native coordinate overlap morphisms

The native homogeneous overlap realizes the change of projective pivot.
The comparison theorem is proved from its localization universal property.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial HomogeneousLocalization
open DeJongAlterations.Geometry.ProjectiveIdeal
open DeJongAlterations.Algebra.Segre

noncomputable section

namespace DeJongAlterations.Geometry.Segre

universe u

attribute [local instance] MvPolynomial.gradedAlgebra homogeneousChartAlgebra overlapAlgebra

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {R : Type u} [CommRing R] {d : ℕ}

/-- The actual native overlap chart immersion. -/
def coordinateOverlapInclusion (i k : Fin (d + 1)) :
    Spec (CommRingCat.of (CoordinateOverlapRing R i k)) ⟶ projectiveSpace R d :=
  Proj.awayι (ProjectiveGrading R d) (MvPolynomial.X i * MvPolynomial.X k)
    (SetLike.mul_mem_graded (MvPolynomial.isHomogeneous_X R i)
      (MvPolynomial.isHomogeneous_X R k)) (by decide : 0 < (1 + 1 : ℕ))

instance coordinateOverlapInclusion_isOpenImmersion (i k : Fin (d + 1)) :
    IsOpenImmersion (coordinateOverlapInclusion (R := R) i k) := by
  unfold coordinateOverlapInclusion
  infer_instance

/-- The first actual affine coordinate restriction has its native projective overlap triangle. -/
@[reassoc]
theorem overlapLeft_coordinateChartInclusion (i k : Fin (d + 1)) :
    Spec.map (CommRingCat.ofHom (overlapLeft (R := R) i k).toRingHom) ≫
        coordinateChartInclusion i =
      coordinateOverlapInclusion i k := by
  rw [coordinateChartInclusion_eq, ← Category.assoc, ← Spec.map_comp]
  have he : (homogeneousChartEquiv (R := R) i).toRingEquiv.toCommRingCatIso.hom ≫
        CommRingCat.ofHom (overlapLeft i k).toRingHom =
      CommRingCat.ofHom
        (awayMap (ProjectiveGrading R d) (MvPolynomial.isHomogeneous_X R k) rfl) := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro z
    change awayMap (ProjectiveGrading R d) (MvPolynomial.isHomogeneous_X R k) rfl
      (homogeneousChartRatioHom i (homogeneousChartDehom i z)) = _
    rw [← AlgHom.comp_apply, homogeneousChartRatioHom_comp_dehom]
    rfl
  rw [he, Proj.SpecMap_awayMap_awayι]
  rfl

/-- The second actual affine coordinate restriction has the same native projective overlap triangle. -/
@[reassoc]
theorem overlapRight_coordinateChartInclusion (i k : Fin (d + 1)) :
    Spec.map (CommRingCat.ofHom (overlapRight (R := R) i k).toRingHom) ≫
        coordinateChartInclusion k =
      coordinateOverlapInclusion i k := by
  rw [coordinateChartInclusion_eq, ← Category.assoc, ← Spec.map_comp]
  have he : (homogeneousChartEquiv (R := R) k).toRingEquiv.toCommRingCatIso.hom ≫
        CommRingCat.ofHom (overlapRight i k).toRingHom =
      CommRingCat.ofHom (awayMap (ProjectiveGrading R d)
        (MvPolynomial.isHomogeneous_X R i) (mul_comm _ _)) := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro z
    change awayMap (ProjectiveGrading R d) (MvPolynomial.isHomogeneous_X R i) (mul_comm _ _)
      (homogeneousChartRatioHom k (homogeneousChartDehom k z)) = _
    rw [← AlgHom.comp_apply, homogeneousChartRatioHom_comp_dehom]
    rfl
  rw [he, Proj.SpecMap_awayMap_awayι]
  rfl

variable {T : Type u} [CommRing T]

/-- The native projective chart maps agree when their actual coordinates differ by an invertible pivot. -/
theorem coordinateChartComparison (i k : Fin (d + 1))
    (f : CoordinateRing R i →+* T) (g : CoordinateRing R k →+* T)
    (hu : IsUnit (f (coordinateDehomCoord i k)))
    (hcoeff : ∀ r : R, f (MvPolynomial.C r) = g (MvPolynomial.C r))
    (hcross : ∀ l, f (coordinateDehomCoord i l) =
      g (coordinateDehomCoord k l) * f (coordinateDehomCoord i k)) :
    Spec.map (CommRingCat.ofHom f) ≫ coordinateChartInclusion i =
      Spec.map (CommRingCat.ofHom g) ≫ coordinateChartInclusion k := by
  let e := overlapLift i k f hu
  have hl : CommRingCat.ofHom f =
      CommRingCat.ofHom (overlapLeft (R := R) i k).toRingHom ≫ CommRingCat.ofHom e := by
    apply CommRingCat.hom_ext
    exact (RingHom.ext (overlapLift_left i k f hu)).symm
  have hr : CommRingCat.ofHom g =
      CommRingCat.ofHom (overlapRight (R := R) i k).toRingHom ≫ CommRingCat.ofHom e := by
    apply CommRingCat.hom_ext
    exact (overlapLift_comp_right i k f g hu hcoeff hcross).symm
  rw [hl, hr, Spec.map_comp, Spec.map_comp, Category.assoc, Category.assoc,
    overlapLeft_coordinateChartInclusion, overlapRight_coordinateChartInclusion]

variable {X : Scheme.{u}}

/-- The actual ring map on global sections induced by a morphism to a spectrum. -/
def pullRingHom {A : CommRingCat.{u}} (f : X ⟶ Spec A) : A →+* Γ(X, ⊤) :=
  ((Scheme.ΓSpecIso A).inv ≫ f.appTop).hom

/-- The actual global-section ring map reconstructs the original affine-target morphism. -/
theorem toSpecΓ_pullRingHom {A : CommRingCat.{u}} (f : X ⟶ Spec A) :
    X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (pullRingHom f)) = f := by
  change X.toSpecΓ ≫ Spec.map ((Scheme.ΓSpecIso A).inv ≫ f.appTop) = f
  rw [Spec.map_comp, ← Scheme.toSpecΓ_naturality_assoc, toSpecΓ_SpecMap_ΓSpecIso_inv,
    Category.comp_id]

/-- Actual pullback of affine coordinates commutes with every ring map. -/
theorem pullRingHom_comp {A B : CommRingCat.{u}} (f : X ⟶ Spec B) (a : A ⟶ B) :
    pullRingHom (f ≫ Spec.map a) = (pullRingHom f).comp a.hom := by
  unfold pullRingHom
  rw [Scheme.Hom.comp_appTop]
  change (((Scheme.ΓSpecIso A).inv ≫ (Spec.map a).appTop) ≫ f.appTop).hom = _
  rw [← Scheme.ΓSpecIso_inv_naturality]
  rfl

/-- Coordinate comparison applies to actual maps from any scheme, via its native global sections. -/
theorem coordinateChartComparison_of_globalSections (i k : Fin (d + 1))
    (f : X ⟶ Spec (CommRingCat.of (CoordinateRing R i)))
    (g : X ⟶ Spec (CommRingCat.of (CoordinateRing R k)))
    (hu : IsUnit (pullRingHom f (coordinateDehomCoord i k)))
    (hcoeff : ∀ r : R, pullRingHom f (MvPolynomial.C r) = pullRingHom g (MvPolynomial.C r))
    (hcross : ∀ l, pullRingHom f (coordinateDehomCoord i l) =
      pullRingHom g (coordinateDehomCoord k l) * pullRingHom f (coordinateDehomCoord i k)) :
    f ≫ coordinateChartInclusion i = g ≫ coordinateChartInclusion k := by
  rw [← toSpecΓ_pullRingHom f, ← toSpecΓ_pullRingHom g, Category.assoc, Category.assoc]
  rw [coordinateChartComparison i k (pullRingHom f) (pullRingHom g) hu hcoeff hcross]

/-- The actual homogeneous overlap immersion has the whole intersection as its range. -/
theorem coordinateOverlapInclusion_opensRange (i k : Fin (d + 1)) :
    (coordinateOverlapInclusion (R := R) i k).opensRange =
      Proj.basicOpen (ProjectiveGrading R d) (MvPolynomial.X i) ⊓
        Proj.basicOpen (ProjectiveGrading R d) (MvPolynomial.X k) := by
  change (Proj.awayι (ProjectiveGrading R d) (MvPolynomial.X i * MvPolynomial.X k) _ _).opensRange = _
  rw [Proj.opensRange_awayι, Proj.basicOpen_mul]

/-- The actual pullback of the two polynomial coordinate chart immersions is the native overlap spectrum. -/
def coordinateChartOverlapIso (i k : Fin (d + 1)) :
    pullback (coordinateChartInclusion (R := R) i) (coordinateChartInclusion k) ≅
      Spec (CommRingCat.of (CoordinateOverlapRing R i k)) :=
  IsOpenImmersion.isoOfRangeEq
    (pullback.fst (coordinateChartInclusion i) (coordinateChartInclusion k) ≫
      coordinateChartInclusion i)
    (coordinateOverlapInclusion i k) (by
      rw [IsOpenImmersion.range_pullback_to_base_of_left]
      change ((coordinateChartInclusion (R := R) i).opensRange ⊓
        (coordinateChartInclusion k).opensRange).1 =
          (coordinateOverlapInclusion i k).opensRange.1
      have hr (l : Fin (d + 1)) :
          (coordinateChartInclusion (R := R) l).opensRange =
            Proj.basicOpen (ProjectiveGrading R d) (MvPolynomial.X l) := by
        unfold coordinateChartInclusion
        rw [Scheme.Hom.opensRange_comp_of_isIso, Scheme.Opens.opensRange_ι]
      rw [hr, hr, coordinateOverlapInclusion_opensRange])

@[reassoc (attr := simp)]
theorem coordinateChartOverlapIso_hom_left (i k : Fin (d + 1)) :
    (coordinateChartOverlapIso (R := R) i k).hom ≫
        Spec.map (CommRingCat.ofHom (overlapLeft (R := R) i k).toRingHom) =
      pullback.fst (coordinateChartInclusion i) (coordinateChartInclusion k) := by
  rw [← cancel_mono (coordinateChartInclusion (R := R) i), Category.assoc,
    overlapLeft_coordinateChartInclusion]
  exact IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

@[reassoc (attr := simp)]
theorem coordinateChartOverlapIso_hom_right (i k : Fin (d + 1)) :
    (coordinateChartOverlapIso (R := R) i k).hom ≫
        Spec.map (CommRingCat.ofHom (overlapRight (R := R) i k).toRingHom) =
      pullback.snd (coordinateChartInclusion i) (coordinateChartInclusion k) := by
  rw [← cancel_mono (coordinateChartInclusion (R := R) k), Category.assoc,
    overlapRight_coordinateChartInclusion, ← pullback.condition]
  exact IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

/-- Coordinate maps agreeing in native projective space produce an actual common-overlap ring map. -/
theorem exists_coordinateOverlap_ringHom (i k : Fin (d + 1))
    (f : X ⟶ Spec (CommRingCat.of (CoordinateRing R i)))
    (g : X ⟶ Spec (CommRingCat.of (CoordinateRing R k)))
    (w : f ≫ coordinateChartInclusion i = g ≫ coordinateChartInclusion k) :
    ∃ h : CoordinateOverlapRing R i k →+* Γ(X, ⊤),
      pullRingHom f = h.comp (overlapLeft i k).toRingHom ∧
      pullRingHom g = h.comp (overlapRight i k).toRingHom := by
  let t := pullback.lift f g w ≫ (coordinateChartOverlapIso i k).hom
  refine ⟨pullRingHom t, ?_, ?_⟩
  · calc
      pullRingHom f = pullRingHom
          (t ≫ Spec.map (CommRingCat.ofHom (overlapLeft i k).toRingHom)) := by
        congr 1
        dsimp only [t]
        rw [Category.assoc, coordinateChartOverlapIso_hom_left, pullback.lift_fst]
      _ = _ := pullRingHom_comp t _
  · calc
      pullRingHom g = pullRingHom
          (t ≫ Spec.map (CommRingCat.ofHom (overlapRight i k).toRingHom)) := by
        congr 1
        dsimp only [t]
        rw [Category.assoc, coordinateChartOverlapIso_hom_right, pullback.lift_snd]
      _ = _ := pullRingHom_comp t _

/-- Actual native equality of projective coordinate maps implies invertibility and every transition equation internally. -/
theorem coordinateChart_transition (i k : Fin (d + 1))
    (f : X ⟶ Spec (CommRingCat.of (CoordinateRing R i)))
    (g : X ⟶ Spec (CommRingCat.of (CoordinateRing R k)))
    (w : f ≫ coordinateChartInclusion i = g ≫ coordinateChartInclusion k) :
    IsUnit (pullRingHom f (coordinateDehomCoord i k)) ∧
      (∀ r : R, pullRingHom f (MvPolynomial.C r) = pullRingHom g (MvPolynomial.C r)) ∧
      ∀ l, pullRingHom f (coordinateDehomCoord i l) =
        pullRingHom g (coordinateDehomCoord k l) * pullRingHom f (coordinateDehomCoord i k) := by
  obtain ⟨h, hf, hg⟩ := exists_coordinateOverlap_ringHom i k f g w
  rw [hf, hg]
  refine ⟨(overlapLeft_pivot_isUnit (R := R) i k).map h, ?_, ?_⟩
  · intro r
    change h (overlapLeft i k (algebraMap R (CoordinateRing R i) r)) =
      h (overlapRight i k (algebraMap R (CoordinateRing R k) r))
    rw [(overlapLeft i k).commutes, (overlapRight i k).commutes]
  · intro l
    change h (overlapLeft i k (coordinateDehomCoord i l)) =
      h (overlapRight i k (coordinateDehomCoord k l)) *
        h (overlapLeft i k (coordinateDehomCoord i k))
    rw [← map_mul, overlap_coordinate_cross]

end DeJongAlterations.Geometry.Segre
