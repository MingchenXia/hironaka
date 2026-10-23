import DeJongAlterations.Geometry.BlowupProjectiveEmbeddingCoefficients
import DeJongAlterations.Geometry.SegreChart
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.RingTheory.TensorProduct.MvPolynomial
import Mathlib.Algebra.Category.Ring.Constructions

/-!
# Actual native projective-space base change over arbitrary coefficient rings

Pure scheme arguments adapted from
`EnvelopeProperty/Projective/NativeBaseChange.lean`, SHA256
`25d601412ca6936de0a9828bb1efd697c2d095cf6ad9bb9ca9279c25dffe0af8`,
and the pure chart comparisons of `EnvelopeProperty/Projective/NativeCharts.lean`, SHA256
`20f23e647db4be70e6d6169c8f61643613a5eb678c39476e2d74b22532e1aeb0`.
No analytic dependency is imported. The coefficient morphism is the already
constructed native `projectiveCoefficientMap`.
-/

open scoped Classical Polynomial
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial
open DeJongAlterations.Geometry.ProjectiveIdeal
open DeJongAlterations.Geometry.BlowupProjectiveEmbedding

noncomputable section

namespace DeJongAlterations.Geometry.ProjectiveSpaceBaseChange

universe u

attribute [local instance] MvPolynomial.gradedAlgebra homogeneousChartAlgebra

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {R S : Type u} [CommRing R] [CommRing S] {n : ℕ}

/-- The existing genuine graded coefficient map, with the chart dimension implicit. -/
abbrev coefficientGradedMap (φ : R →+* S) : ProjectiveGrading R n →+*ᵍ ProjectiveGrading S n :=
  polynomialCoefficientMap φ n

@[simp]
theorem coefficientGradedMap_apply (φ : R →+* S) (F : MvPolynomial (Fin (n + 1)) R) :
    coefficientGradedMap φ F = MvPolynomial.map φ F := rfl

/-- The existing native irrelevant-containment proof for the actual coefficient map. -/
theorem coefficientGradedMap_irrelevant_le (φ : R →+* S) :
    HomogeneousIdeal.irrelevant (ProjectiveGrading S n) ≤
      (HomogeneousIdeal.irrelevant (ProjectiveGrading R n)).map (coefficientGradedMap φ) :=
  polynomialCoefficientMap_irrelevant φ n

/-- Alias of the already constructed genuine projective coefficient morphism. -/
abbrev nativeCoefficientMap (φ : R →+* S) : NativeProjectiveScheme S n ⟶ NativeProjectiveScheme R n :=
  projectiveCoefficientMap φ n

/-- Alias of the actual original-coefficient projective structure morphism. -/
abbrev nativeStructureMap : NativeProjectiveScheme R n ⟶ Spec (CommRingCat.of R) :=
  projectiveSpaceStructure R n

set_option backward.isDefEq.respectTransparency false in
/-- The constructed chart morphism is the canonical Mathlib homogeneous-fraction chart. -/
theorem nativeHomogeneousChartSchemeIso_hom_eq (j : Fin (n + 1)) :
    (nativeHomogeneousChartSchemeIso (R := R) j).hom =
      AlgebraicGeometry.Proj.basicOpenToSpec (ProjectiveGrading R n) (MvPolynomial.X j) := by
  apply Scheme.fullyFaithfulForgetToLocallyRingedSpace.map_injective
  change ProjectiveSpectrum.Proj.toSpec (ProjectiveGrading R n) (MvPolynomial.X j) = _
  symm
  refine Eq.trans ?_ (ΓSpec.locallyRingedSpaceAdjunction.homEquiv_apply _ _ _).symm
  dsimp [AlgebraicGeometry.Proj.basicOpenToSpec, Scheme.Opens.toSpecΓ]
  simp only [Category.assoc, ← Spec.map_comp]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Equality with the actual canonical Mathlib Proj coordinate-chart isomorphism. -/
theorem nativeHomogeneousChartSchemeIso_eq (j : Fin (n + 1)) :
    nativeHomogeneousChartSchemeIso (R := R) j =
      AlgebraicGeometry.Proj.basicOpenIsoSpec (ProjectiveGrading R n) (MvPolynomial.X j)
        (MvPolynomial.isHomogeneous_X R j) (by decide : 0 < (1 : ℕ)) := by
  apply Iso.ext
  exact nativeHomogeneousChartSchemeIso_hom_eq j

/-- The actual affine coordinate chart inclusion into the native polynomial Proj scheme. -/
def nativeCoordinateInclusion (j : Fin (n + 1)) :
    Spec (CommRingCat.of (CoordinateRing R j)) ⟶ NativeProjectiveScheme R n :=
  (nativeCoordinateSchemeIso j).inv ≫ (nativeCoordinateOpen j).ι

/-- The genuine coordinate chart inclusion is an actual scheme open immersion. -/
theorem nativeCoordinateInclusion_isOpenImmersion (j : Fin (n + 1)) :
    IsOpenImmersion (nativeCoordinateInclusion (R := R) j) := by
  unfold nativeCoordinateInclusion
  infer_instance

private local instance nativeCoordinateInclusion_openImmersion (j : Fin (n + 1)) :
    IsOpenImmersion (nativeCoordinateInclusion (R := R) j) :=
  nativeCoordinateInclusion_isOpenImmersion j

/-- Its scheme image is exactly the genuine coordinate open. -/
theorem nativeCoordinateInclusion_opensRange (j : Fin (n + 1)) :
    (nativeCoordinateInclusion (R := R) j).opensRange = nativeCoordinateOpen j :=
  (Scheme.Hom.opensRange_comp_of_isIso _ _).trans (nativeCoordinateOpen j).opensRange_ι

/-- These actual coordinate inclusions agree with the released Segre chart inclusions. -/
theorem nativeCoordinateInclusion_eq_segre (j : Fin (n + 1)) :
    nativeCoordinateInclusion (R := R) j = Segre.coordinateChartInclusion (R := R) j := by
  unfold nativeCoordinateInclusion nativeCoordinateSchemeIso
    Segre.coordinateChartInclusion Segre.coordinateChartIso
  rw [nativeHomogeneousChartSchemeIso_eq]
  rfl

/-- The actual chart preserves its original coefficient structure map. -/
theorem nativeCoordinateChart_over_base (j : Fin (n + 1)) :
    nativeCoordinateInclusion (R := R) j ≫ nativeStructureMap =
      Spec.map (CommRingCat.ofHom (algebraMap R (CoordinateRing R j))) := by
  rw [nativeCoordinateInclusion_eq_segre]
  exact Segre.coordinateChartInclusion_structure j

/-- The full native coordinate-open preimage is the same coordinate open over the new base. -/
theorem nativeCoefficientMap_preimage_coordinateOpen (φ : R →+* S) (j : Fin (n + 1)) :
    nativeCoefficientMap φ ⁻¹ᵁ nativeCoordinateOpen j = nativeCoordinateOpen (R := S) j := by
  change AlgebraicGeometry.Proj.map _ _ ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen _ (X j) = _
  rw [AlgebraicGeometry.Proj.map_preimage_basicOpen]
  simp only [coefficientGradedMap_apply, MvPolynomial.map_X]
  rfl

/-- The actual homogeneous coordinate localization map, with the mapped denominator identified. -/
def homogeneousCoordinateMap (φ : R →+* S) (j : Fin (n + 1)) :
    HomogeneousChartRing R j →+* HomogeneousChartRing S j := by
  exact HomogeneousLocalization.map (coefficientGradedMap φ)
    (P := Submonoid.powers (X j)) (Q := Submonoid.powers (X j)) (by
      rintro _ ⟨d, rfl⟩
      exact ⟨d, by simp only [map_pow, coefficientGradedMap_apply, MvPolynomial.map_X]⟩)

set_option backward.isDefEq.respectTransparency false in
/-- The entire homogeneous chart square, before replacing actual fractions by affine coordinates. -/
theorem nativeCoefficientMap_homogeneousChart (φ : R →+* S) (j : Fin (n + 1)) :
    (nativeHomogeneousChartSchemeIso (R := S) j).inv ≫ (nativeCoordinateOpen j).ι ≫
      nativeCoefficientMap φ =
        Spec.map (CommRingCat.ofHom (homogeneousCoordinateMap φ j)) ≫
          (nativeHomogeneousChartSchemeIso (R := R) j).inv ≫ (nativeCoordinateOpen j).ι := by
  rw [nativeHomogeneousChartSchemeIso_eq, nativeHomogeneousChartSchemeIso_eq]
  change _ ≫ (AlgebraicGeometry.Proj.basicOpen (ProjectiveGrading S n) (X j)).ι ≫ _ =
    _ ≫ _ ≫ (AlgebraicGeometry.Proj.basicOpen (ProjectiveGrading R n) (X j)).ι
  rw [← Category.assoc]
  erw [AlgebraicGeometry.Proj.basicOpenIsoSpec_inv_ι]
  erw [AlgebraicGeometry.Proj.basicOpenIsoSpec_inv_ι]
  have aux (s : MvPolynomial (Fin (n + 1)) S)
      (hs : s ∈ ProjectiveGrading S n 1) (he : coefficientGradedMap φ (X j) = s) :
      AlgebraicGeometry.Proj.awayι (ProjectiveGrading S n) s hs (by decide : 0 < (1 : ℕ)) ≫
        nativeCoefficientMap φ =
          Spec.map (CommRingCat.ofHom (HomogeneousLocalization.map (coefficientGradedMap φ)
            (P := Submonoid.powers (X j)) (Q := Submonoid.powers s) (by
              rintro _ ⟨d, rfl⟩
              exact ⟨d, by simp only [map_pow, he]⟩))) ≫
            AlgebraicGeometry.Proj.awayι (ProjectiveGrading R n) (X j)
              (MvPolynomial.isHomogeneous_X R j) (by decide : 0 < (1 : ℕ)) := by
    subst s
    exact AlgebraicGeometry.Proj.awayι_comp_map (coefficientGradedMap φ)
      (coefficientGradedMap_irrelevant_le φ) (by decide : 0 < (1 : ℕ))
      (X j) (MvPolynomial.isHomogeneous_X R j)
  exact aux (X j) (MvPolynomial.isHomogeneous_X S j)
    (by simp only [coefficientGradedMap_apply, MvPolynomial.map_X])

/-- Dehomogenizing commutes with the entire coefficient polynomial map. -/
theorem coordinateDehom_map (φ : R →+* S) (j : Fin (n + 1))
    (F : MvPolynomial (Fin (n + 1)) R) :
    coordinateDehom j (MvPolynomial.map φ F) = MvPolynomial.map φ (coordinateDehom j F) := by
  induction F using MvPolynomial.induction_on with
  | C r =>
    simp only [MvPolynomial.map_C, coordinateDehom, MvPolynomial.aeval_C]
    exact (MvPolynomial.map_C φ r).symm
  | add F G hF hG => simp only [map_add, hF, hG]
  | mul_X F i hF =>
    simp only [map_mul, MvPolynomial.map_X, coordinateDehom, MvPolynomial.aeval_X] at *
    rw [hF]
    congr 1
    by_cases h : i = j
    · simp only [coordinateDehomCoord, dif_pos h, map_one]
    · simp only [coordinateDehomCoord, dif_neg h, MvPolynomial.map_X]

set_option backward.isDefEq.respectTransparency false in
/-- The actual homogeneous coordinate map preserves every original dehomogenized fraction. -/
theorem homogeneousCoordinateMap_dehom (φ : R →+* S) (j : Fin (n + 1))
    (a : HomogeneousChartRing R j) :
    homogeneousChartDehom j (homogeneousCoordinateMap φ j a) =
      MvPolynomial.map φ (homogeneousChartDehom j a) := by
  obtain ⟨d, F, hF, rfl⟩ := a.mk_surjective (ProjectiveGrading R n) (MvPolynomial.isHomogeneous_X R j)
  have he : homogeneousCoordinateMap φ j
      (HomogeneousLocalization.Away.mk (ProjectiveGrading R n)
        (MvPolynomial.isHomogeneous_X R j) d F hF) =
        HomogeneousLocalization.Away.mk (ProjectiveGrading S n)
          (MvPolynomial.isHomogeneous_X S j) d (MvPolynomial.map φ F) (hF.map φ) := by
    apply HomogeneousLocalization.val_injective
    dsimp only [homogeneousCoordinateMap, HomogeneousLocalization.Away.mk]
    rw [HomogeneousLocalization.map_mk]
    simp only [HomogeneousLocalization.val_mk, coefficientGradedMap_apply]
    congr 1
    apply Subtype.ext
    simp only [map_pow, MvPolynomial.map_X]
  rw [he]
  rw [homogeneousChartDehom_mk, homogeneousChartDehom_mk]
  exact coordinateDehom_map φ j F

/-- The entire homogeneous-coordinate-ring map is conjugate to coefficient polynomial mapping. -/
theorem homogeneousCoordinateMap_equiv (φ : R →+* S) (j : Fin (n + 1)) :
    (homogeneousChartEquiv (R := S) j).toRingHom.comp (homogeneousCoordinateMap φ j) =
      (MvPolynomial.map φ).comp (homogeneousChartEquiv (R := R) j).toRingHom := by
  apply RingHom.ext
  intro a
  exact homogeneousCoordinateMap_dehom φ j a

set_option backward.isDefEq.respectTransparency false in
/-- Every actual scheme coordinate chart preserves the whole coefficient polynomial map. -/
theorem nativeCoefficientMap_coordinateChart (φ : R →+* S) (j : Fin (n + 1)) :
    nativeCoordinateInclusion (R := S) j ≫ nativeCoefficientMap φ =
      Spec.map (CommRingCat.ofHom (MvPolynomial.map φ : CoordinateRing R j →+* CoordinateRing S j)) ≫
        nativeCoordinateInclusion (R := R) j := by
  have h : Spec.map (CommRingCat.ofHom (homogeneousChartEquiv (R := S) j).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (homogeneousCoordinateMap φ j)) =
        Spec.map (CommRingCat.ofHom (MvPolynomial.map φ : CoordinateRing R j →+* CoordinateRing S j)) ≫
          Spec.map (CommRingCat.ofHom (homogeneousChartEquiv (R := R) j).toRingHom) := by
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    exact homogeneousCoordinateMap_equiv φ j
  change (Spec.map (CommRingCat.ofHom (homogeneousChartEquiv (R := S) j).toRingHom) ≫
    (nativeHomogeneousChartSchemeIso j).inv ≫ (nativeCoordinateOpen j).ι) ≫ _ =
      _ ≫ Spec.map (CommRingCat.ofHom (homogeneousChartEquiv (R := R) j).toRingHom) ≫
        (nativeHomogeneousChartSchemeIso j).inv ≫ (nativeCoordinateOpen j).ι
  simp only [Category.assoc]
  rw [nativeCoefficientMap_homogeneousChart, ← Category.assoc, h, Category.assoc]

/-- The coefficient chart square is a genuine open-immersion pullback. -/
theorem isPullback_nativeCoefficientMap_coordinateChart (φ : R →+* S) (j : Fin (n + 1)) :
    IsPullback
      (Spec.map (CommRingCat.ofHom (MvPolynomial.map φ : CoordinateRing R j →+* CoordinateRing S j)))
      (nativeCoordinateInclusion (R := S) j) (nativeCoordinateInclusion (R := R) j)
      (nativeCoefficientMap φ) := by
  have := nativeCoordinateInclusion_isOpenImmersion (R := R) j
  have := nativeCoordinateInclusion_isOpenImmersion (R := S) j
  apply IsOpenImmersion.isPullback
  · exact nativeCoefficientMap_coordinateChart φ j
  · rw [nativeCoordinateInclusion_opensRange, nativeCoordinateInclusion_opensRange,
      nativeCoefficientMap_preimage_coordinateOpen]

/-- A genuine scheme coordinate cover, with the actual affine polynomial chart inclusions. -/
def nativeCoordinateCover : (NativeProjectiveScheme R n).OpenCover :=
  Scheme.Cover.mkOfCovers (P := @IsOpenImmersion) (Fin (n + 1))
    (fun j => Spec (CommRingCat.of (CoordinateRing R j))) (fun j => nativeCoordinateInclusion j)
    (by
      intro p
      have hp : p ∈ ⨆ j : Fin (n + 1), nativeCoordinateOpen (R := R) j := by
        have htop : (⨆ i : Fin (n + 1), nativeCoordinateOpen (R := R) i) = ⊤ := by
          apply AlgebraicGeometry.Proj.iSup_basicOpen_eq_top
          rw [irrelevant_eq_idealOfVars, MvPolynomial.idealOfVars]
        rw [htop]
        trivial
      obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.mp hp
      have := nativeCoordinateInclusion_isOpenImmersion (R := R) j
      have hmem : p ∈ Set.range (nativeCoordinateInclusion (R := R) j) := by
        change p ∈ (nativeCoordinateInclusion (R := R) j).opensRange
        rw [nativeCoordinateInclusion_opensRange]
        exact hj
      obtain ⟨q, hq⟩ := hmem
      exact ⟨j, q, hq⟩)
    (fun j => nativeCoordinateInclusion_isOpenImmersion j)

/-- The actual polynomial coordinate tensor square becomes a genuine affine scheme pullback. -/
theorem isPullback_coordinatePolynomialBaseChange [Algebra R S] (j : Fin (n + 1)) :
    IsPullback
      (Spec.map (CommRingCat.ofHom
        (MvPolynomial.map (algebraMap R S) : CoordinateRing R j →+* CoordinateRing S j)))
      (Spec.map (CommRingCat.ofHom (algebraMap S (CoordinateRing S j))))
      (Spec.map (CommRingCat.ofHom (algebraMap R (CoordinateRing R j))))
      (Spec.map (CommRingCat.ofHom (algebraMap R S))) := by
  let : Algebra (CoordinateRing R j) (CoordinateRing S j) := MvPolynomial.algebraMvPolynomial
  have h := CommRingCat.isPushout_of_isPushout R S (CoordinateRing R j) (CoordinateRing S j)
  have hp := isPullback_SpecMap_of_isPushout _ _ _ _ h
  exact hp.flip

set_option backward.isDefEq.respectTransparency false in
/-- The actual original-base polynomial Proj square is cartesian over every coefficient homomorphism. -/
theorem isPullback_nativeCoefficientBaseChange (φ : R →+* S) :
    IsPullback (nativeCoefficientMap (n := n) φ) (nativeStructureMap (R := S) (n := n))
      (nativeStructureMap (R := R) (n := n)) (Spec.map (CommRingCat.ofHom φ)) := by
  let : Algebra R S := φ.toAlgebra
  apply Scheme.isPullback_of_openCover _ _ _ _ (nativeCoordinateCover (R := R) (n := n))
  intro j
  change Fin (n + 1) at j
  change IsPullback (pullback.snd (nativeCoefficientMap φ) (nativeCoordinateInclusion j))
    (pullback.fst (nativeCoefficientMap φ) (nativeCoordinateInclusion j) ≫ nativeStructureMap)
    (nativeCoordinateInclusion j ≫ nativeStructureMap) (Spec.map (CommRingCat.ofHom φ))
  have hR : nativeCoordinateInclusion (R := R) j ≫ nativeStructureMap =
      Spec.map (CommRingCat.ofHom (algebraMap R (CoordinateRing R j))) :=
    nativeCoordinateChart_over_base j
  have hS : nativeCoordinateInclusion (R := S) j ≫ nativeStructureMap =
      Spec.map (CommRingCat.ofHom (algebraMap S (CoordinateRing S j))) :=
    nativeCoordinateChart_over_base j
  rw [hR]
  let e := (isPullback_nativeCoefficientMap_coordinateChart φ j).flip.isoPullback
  apply (isPullback_coordinatePolynomialBaseChange (R := R) (S := S) j).of_iso e
    (Iso.refl _) (Iso.refl _) (Iso.refl _)
  · exact (isPullback_nativeCoefficientMap_coordinateChart φ j).flip.isoPullback_hom_snd.symm
  · change _ = e.hom ≫ pullback.fst (nativeCoefficientMap φ) (nativeCoordinateInclusion j) ≫ _
    rw [← Category.assoc,
      (isPullback_nativeCoefficientMap_coordinateChart φ j).flip.isoPullback_hom_fst, hS]
    exact Category.comp_id _
  · rfl
  · rfl

/-- The actual already constructed projective coefficient map forms a
Cartesian square over every homomorphism of arbitrary commutative rings. -/
theorem isPullback_projectiveCoefficientMap (f : R →+* S) (m : ℕ) :
    IsPullback (projectiveCoefficientMap f m) (projectiveSpaceStructure S m)
      (projectiveSpaceStructure R m) (Spec.map (CommRingCat.ofHom f)) :=
  isPullback_nativeCoefficientBaseChange (n := m) f

/-- The genuine base-change isomorphism of native projective spaces. -/
def projectiveSpaceBaseChangeIso (f : R →+* S) (m : ℕ) :
    projectiveSpace S m ≅ pullback (projectiveSpaceStructure R m)
      (Spec.map (CommRingCat.ofHom f)) :=
  (isPullback_projectiveCoefficientMap f m).isoPullback

/-- The original whole projective coefficient map is the actual first projection. -/
@[reassoc]
theorem projectiveSpaceBaseChangeIso_hom_fst (f : R →+* S) (m : ℕ) :
    (projectiveSpaceBaseChangeIso f m).hom ≫ pullback.fst _ _ =
      projectiveCoefficientMap f m :=
  (isPullback_projectiveCoefficientMap f m).isoPullback_hom_fst

/-- The original whole coefficient structure map is the actual second projection. -/
@[reassoc]
theorem projectiveSpaceBaseChangeIso_hom_snd (f : R →+* S) (m : ℕ) :
    (projectiveSpaceBaseChangeIso f m).hom ≫ pullback.snd _ _ =
      projectiveSpaceStructure S m :=
  (isPullback_projectiveCoefficientMap f m).isoPullback_hom_snd

end DeJongAlterations.Geometry.ProjectiveSpaceBaseChange
