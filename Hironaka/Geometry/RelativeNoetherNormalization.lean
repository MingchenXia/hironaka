import Hironaka.Algebra.RelativeNoetherNormalizationFinite
import Hironaka.Geometry.FiberDimensionGenericFinite
import Hironaka.Geometry.AffineGenericFlatness
import Mathlib.Algebra.Category.Ring.Constructions

/-!
# Actual finite surjective relative normalization projections

The finite polynomial map is internally constructed from the original
finite-type domain algebra. Its native spectrum projection is finite and
surjective with the literal coefficient triangle. Actual localization
pullback squares identify the original principal-open restriction, and its
actual fibers have the computed constant dimension on that open.
This does not assert general fiber-dimension upper semicontinuity.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace Hironaka.Geometry.RelativeNoetherNormalization

open FiberDimensionGenericFinite

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]

/-- The actual localized structure map uses the localization of the original coefficient map. -/
def localizedStructure (b : R) :
    Spec (.of (Localization.Away (algebraMap R A b))) ⟶ Spec (.of (Localization.Away b)) :=
  Spec.map (CommRingCat.ofHom (Localization.awayMap (algebraMap R A) b))

/-- The actual localized source projects to the original affine source. -/
def originalProjection (b : R) :
    Spec (.of (Localization.Away (algebraMap R A b))) ⟶ Spec (.of A) :=
  Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away (algebraMap R A b))))

/-- The literal localization square is an actual scheme pullback. -/
theorem isPullback_localized (b : R) :
    IsPullback (localizedStructure R A b) (originalProjection R A b)
      (AffineGenericFlatness.affineStructure R (Localization.Away b))
      (AffineGenericFlatness.affineStructure R A) := by
  have : IsLocalization ((Submonoid.powers b).map (algebraMap R A))
      (Localization.Away (algebraMap R A b)) := by
    rw [Submonoid.map_powers]
    infer_instance
  have hw : (Localization.awayMap (algebraMap R A) b).comp
      (algebraMap R (Localization.Away b)) =
        (algebraMap A (Localization.Away (algebraMap R A b))).comp (algebraMap R A) := by
    apply RingHom.ext
    intro r
    simp [Localization.awayMap, IsLocalization.Away.map]
  exact (isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_of_isLocalization (algebraMap R A)
      (Localization.awayMap (algebraMap R A) b) hw (Submonoid.powers b))).flip

/-- The original principal-open restriction has the actual localized source as its scheme model. -/
def restrictionIso (b : R) :
    (AffineGenericFlatness.affineStructure R A ⁻¹ᵁ PrimeSpectrum.basicOpen b).toScheme ≅
      Spec (.of (Localization.Away (algebraMap R A b))) :=
  (AffineGenericFlatness.isPullback_restrictedAffine R A b).isoIsPullback _ _
    (isPullback_localized R A b)

/-- The actual source comparison preserves the localized coefficient triangle. -/
@[reassoc]
theorem restrictionIso_hom_structure (b : R) :
    (restrictionIso R A b).hom ≫ localizedStructure R A b =
      (AffineGenericFlatness.affineStructure R A ∣_ PrimeSpectrum.basicOpen b) ≫
        (basicOpenIsoSpecAway (R := CommRingCat.of R) b).hom :=
  (AffineGenericFlatness.isPullback_restrictedAffine R A b).isoIsPullback_hom_fst _ _
    (isPullback_localized R A b)

/-- The actual source comparison preserves projection to the original affine source. -/
@[reassoc]
theorem restrictionIso_hom_originalProjection (b : R) :
    (restrictionIso R A b).hom ≫ originalProjection R A b =
      (AffineGenericFlatness.affineStructure R A ⁻¹ᵁ PrimeSpectrum.basicOpen b).ι :=
  (AffineGenericFlatness.isPullback_restrictedAffine R A b).isoIsPullback_hom_snd _ _
    (isPullback_localized R A b)

/-- An actual isomorphism of the original restricted and native localized affine arrows. -/
def restrictionArrowIso (b : R) :
    Arrow.mk (AffineGenericFlatness.affineStructure R A ∣_ PrimeSpectrum.basicOpen b) ≅
      Arrow.mk (localizedStructure R A b) :=
  Arrow.isoMk (restrictionIso R A b) (basicOpenIsoSpecAway (R := CommRingCat.of R) b)
    (restrictionIso_hom_structure R A b)

/-- The original finite-type domain algebra internally constructs a finite surjective
projection to actual relative affine space, and computes all its actual localized fiber dimensions. -/
theorem exists_principal_finite_surjective_projection [IsDomain R] [IsDomain A]
    [Algebra.FiniteType R A] (hinj : Function.Injective (algebraMap R A)) :
    ∃ b : R, b ≠ 0 ∧ ∃ (n : ℕ)
      (q : Spec (.of (Localization.Away (algebraMap R A b))) ⟶
        Spec (.of (MvPolynomial (Fin n) (Localization.Away b)))),
      IsFinite q ∧ Surjective q ∧ q ≫ affineSpaceStructure (Localization.Away b) n =
        localizedStructure R A b ∧
      ∀ s : PrimeSpectrum (Localization.Away b),
        FiberDimension.fiberDimension (localizedStructure R A b) s = n := by
  obtain ⟨b, hb, n, g, hg, hfin, hC⟩ :=
    Algebra.RelativeNoetherNormalizationFinite.exists_finite_injective_polynomial_map hinj
  let q := Spec.map (CommRingCat.ofHom g)
  have : IsFinite q := (IsFinite.SpecMap_iff _).mpr hfin
  have : Surjective q := ⟨hfin.to_isIntegral.comap_surjective hg⟩
  have hbase : q ≫ affineSpaceStructure (Localization.Away b) n = localizedStructure R A b := by
    dsimp only [q, affineSpaceStructure, localizedStructure]
    rw [← Spec.map_comp]
    congr 1
    exact CommRingCat.hom_ext hC
  refine ⟨b, hb, n, q, inferInstance, inferInstance, hbase, ?_⟩
  intro s
  rw [← hbase]
  exact finiteProjection_fiber_dimension q s

/-- The actual original principal-open source admits the internally constructed
finite surjective projection, preserving its literal restricted coefficient map. -/
theorem exists_principal_restriction_finite_surjective_projection [IsDomain R] [IsDomain A]
    [Algebra.FiniteType R A] (hinj : Function.Injective (algebraMap R A)) :
    ∃ b : R, b ≠ 0 ∧ ∃ (n : ℕ)
      (q : (AffineGenericFlatness.affineStructure R A ⁻¹ᵁ PrimeSpectrum.basicOpen b).toScheme ⟶
        Spec (.of (MvPolynomial (Fin n) (Localization.Away b)))),
      IsFinite q ∧ Surjective q ∧ q ≫ affineSpaceStructure (Localization.Away b) n =
        (AffineGenericFlatness.affineStructure R A ∣_ PrimeSpectrum.basicOpen b) ≫
          (basicOpenIsoSpecAway (R := CommRingCat.of R) b).hom := by
  obtain ⟨b, hb, n, q, hfin, hsurj, hbase, hdim⟩ :=
    exists_principal_finite_surjective_projection R A hinj
  let : IsFinite q := hfin
  let : Surjective q := hsurj
  refine ⟨b, hb, n, (restrictionIso R A b).hom ≫ q, inferInstance, inferInstance, ?_⟩
  rw [Category.assoc, hbase, restrictionIso_hom_structure]

/-- The actual original principal-base-open restriction has internally computed constant fiber dimension. -/
theorem exists_nonzero_constant_fiberDimension_morphismRestrict [IsDomain R] [IsDomain A]
    [Algebra.FiniteType R A] (hinj : Function.Injective (algebraMap R A)) :
    ∃ b : R, b ≠ 0 ∧ ∃ n : ℕ, Nonempty (PrimeSpectrum.basicOpen b) ∧
      Dense (PrimeSpectrum.basicOpen b : Set (PrimeSpectrum R)) ∧
      ∀ s : PrimeSpectrum.basicOpen b,
        FiberDimension.fiberDimension
          (AffineGenericFlatness.affineStructure R A ∣_ PrimeSpectrum.basicOpen b) s = n := by
  obtain ⟨b, hb, n, q, hqfin, hqsurj, hbase, hdim⟩ :=
    exists_principal_finite_surjective_projection R A hinj
  refine ⟨b, hb, n, AffineGenericFlatness.basicOpen_nonempty_of_ne_zero R hb,
    AffineGenericFlatness.basicOpen_dense_of_ne_zero R hb, ?_⟩
  intro s
  exact (fiberDimension_eq_of_arrowIso (restrictionArrowIso R A b) s).trans (hdim _)

end Hironaka.Geometry.RelativeNoetherNormalization
