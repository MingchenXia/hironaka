/-
Copyright (c) 2026. All rights reserved.
-/
import DeJongAlterations.Geometry.ProjectiveIdealCoordinateIdeal
import DeJongAlterations.Geometry.ProjectiveIdealStalk
import Mathlib.RingTheory.Localization.Ideal
/- Reused from EnvelopeProperty/Projective/IdealRepresentation.lean; SHA256 f4fbcfe0a1b2f3c1ee052254f20054bb393519144bb1aca2b5eebeca459e9c49. -/


/-!
# Actual ideal sheaves represented by original homogeneous ideals

The homogeneous representative is constructed from the actual ideal sheaf's
whole coordinate ideals. Genuine homogeneous fraction lifts, true overlap
stalk identities and actual affine localization clear denominators on the
finite coordinate cover. No representation, chart-ideal, radical, center
or norm certificate is an input. The base ring is arbitrary; finite
generation and analytic coherence require separate genuine producers.
-/

open scoped Classical
open CategoryTheory AlgebraicGeometry HomogeneousLocalization MvPolynomial
open Opposite
noncomputable section
universe u
namespace DeJongAlterations.Geometry.ProjectiveIdeal
attribute [local instance] MvPolynomial.gradedAlgebra
variable {R : Type u} [CommRing R] {n : ℕ}

private local instance idealRepresentationHomogeneousAlgebra (j : Fin (n + 1)) :
    Algebra R (HomogeneousChartRing R j) := homogeneousChartAlgebra j

private theorem homogeneous_mem_degree_smul
    {F : MvPolynomial (Fin (n + 1)) R} {d : ℕ} (hF : F.IsHomogeneous d) :
    F ∈ ProjectiveGrading R n (d • (1 : ℕ)) := by
  change F.IsHomogeneous (d • (1 : ℕ))
  simpa only [smul_eq_mul, mul_one] using hF

/-- The actual ideal sheaf's entire polynomial ideal on a true coordinate chart. -/
def nativeCoordinateIdeal (I : (NativeProjectiveScheme R n).IdealSheafData) (j : Fin (n + 1)) :
    Ideal (CoordinateRing R j) :=
  (I.ideal ⟨nativeCoordinateOpen j, nativeCoordinateOpen_isAffine j⟩).comap
    (nativeCoordinateSectionsIso (R := R) j).hom.hom

/-- The original homogeneous ideal constructed from all actual coordinate ideals. -/
def nativeHomogeneousRepresentative (I : (NativeProjectiveScheme R n).IdealSheafData) :
    HomogeneousIdeal (ProjectiveGrading R n) :=
  Ideal.homogeneousCore (ProjectiveGrading R n)
    (⨅ j : Fin (n + 1), (nativeCoordinateIdeal I j).comap (coordinateDehom j).toRingHom)

/-- Every constructed representative element has its entire dehomogenization in each original chart ideal. -/
theorem nativeHomogeneousRepresentative_dehom_le
    (I : (NativeProjectiveScheme R n).IdealSheafData) (j : Fin (n + 1)) :
    (nativeHomogeneousRepresentative I).toIdeal.map (coordinateDehom j).toRingHom ≤
      nativeCoordinateIdeal I j := by
  rw [Ideal.map_le_iff_le_comap]
  exact (Ideal.toIdeal_homogeneousCore_le _ _).trans (iInf_le _ j)

/-- Actual homogeneous form membership is equivalent to original whole chart-ideal membership everywhere. -/
theorem mem_nativeHomogeneousRepresentative_of_isHomogeneous
    (I : (NativeProjectiveScheme R n).IdealSheafData)
    {F : MvPolynomial (Fin (n + 1)) R} {d : ℕ} (hF : F.IsHomogeneous d) :
    F ∈ nativeHomogeneousRepresentative I ↔ ∀ j, coordinateDehom j F ∈ nativeCoordinateIdeal I j := by
  constructor
  · intro h j
    exact nativeHomogeneousRepresentative_dehom_le I j
      (Ideal.mem_map_of_mem (coordinateDehom j).toRingHom h)
  · intro h
    exact Ideal.mem_homogeneousCore_of_homogeneous_of_mem ⟨d, hF⟩
      (Ideal.mem_iInf.mpr fun j => h j)

/-- Every whole coordinate polynomial has a genuine original homogeneous numerator, supplied by the true fraction chart. -/
theorem exists_homogeneous_coordinateDehom (j : Fin (n + 1)) (a : CoordinateRing R j) :
    ∃ (d : ℕ) (F : MvPolynomial (Fin (n + 1)) R), F.IsHomogeneous d ∧ coordinateDehom j F = a := by
  obtain ⟨d, F, hF, he⟩ := Away.mk_surjective (ProjectiveGrading R n)
    (MvPolynomial.isHomogeneous_X R j) (homogeneousChartRatioHom j a)
  refine ⟨d, F, ?_, ?_⟩
  · change F.IsHomogeneous (d • (1 : ℕ)) at hF
    simpa only [smul_eq_mul, mul_one] using hF
  · rw [← homogeneousChartDehom_mk j d F hF, he]
    exact AlgHom.congr_fun (homogeneousChartDehom_comp_ratioHom j) a

/-- The actual affine section of every whole original polynomial after dehomogenization. -/
def nativeFormSection (j : Fin (n + 1)) (F : MvPolynomial (Fin (n + 1)) R) :
    Γ(NativeProjectiveScheme R n, nativeCoordinateOpen j) :=
  (nativeCoordinateSectionsIso (R := R) j).hom (coordinateDehom j F)

/-- A homogeneous form's whole ratio is its genuine degree-zero fraction. -/
theorem homogeneousChartRatioHom_dehom_of_isHomogeneous (j : Fin (n + 1))
    {F : MvPolynomial (Fin (n + 1)) R} {d : ℕ} (hF : F.IsHomogeneous d) :
    homogeneousChartRatioHom j (coordinateDehom j F) =
      Away.mk (ProjectiveGrading R n) (MvPolynomial.isHomogeneous_X R j) d F
        (homogeneous_mem_degree_smul hF) := by
  rw [← homogeneousChartDehom_mk j d F, ← AlgHom.comp_apply,
    homogeneousChartRatioHom_comp_dehom, AlgHom.id_apply]

set_option backward.isDefEq.respectTransparency false in
/-- Every original homogeneous-form section germ equals its actual degree-zero prime-localized fraction in the true projective stalk. -/
theorem nativeFormSection_germ (j : Fin (n + 1)) (p : NativeProjectiveScheme R n)
    (hp : p ∈ nativeCoordinateOpen j) {F : MvPolynomial (Fin (n + 1)) R} {d : ℕ}
    (hF : F.IsHomogeneous d) :
    (AlgebraicGeometry.Proj.stalkIso' (ProjectiveGrading R n) p)
      ((NativeProjectiveScheme R n).presheaf.germ (nativeCoordinateOpen j) p hp
        (nativeFormSection j F)) =
      HomogeneousLocalization.mapId (ProjectiveGrading R n) (Submonoid.powers_le.mpr hp)
        (Away.mk (ProjectiveGrading R n) (MvPolynomial.isHomogeneous_X R j) d F
          (homogeneous_mem_degree_smul hF)) := by
  change (AlgebraicGeometry.Proj.stalkIso' (ProjectiveGrading R n) p)
    ((NativeProjectiveScheme R n).presheaf.germ (nativeCoordinateOpen j) p hp
      ((nativeHomogeneousChartSectionsIso (R := R) j).hom
        (homogeneousChartRatioHom j (coordinateDehom j F)))) = _
  rw [homogeneousChartRatioHom_dehom_of_isHomogeneous j hF]
  have hg := congrArg (fun f => f
      (Away.mk (ProjectiveGrading R n) (MvPolynomial.isHomogeneous_X R j) d F
        (homogeneous_mem_degree_smul hF)))
    (nativeHomogeneousChartSectionsIso_germ (R := R) j p hp)
  change (NativeProjectiveScheme R n).presheaf.germ (nativeCoordinateOpen j) p hp
      ((nativeHomogeneousChartSectionsIso (R := R) j).hom
        (Away.mk (ProjectiveGrading R n) (MvPolynomial.isHomogeneous_X R j) d F
          (homogeneous_mem_degree_smul hF))) =
    (AlgebraicGeometry.Proj.stalkIso' (ProjectiveGrading R n) p).symm
      (HomogeneousLocalization.mapId (ProjectiveGrading R n) (Submonoid.powers_le.mpr hp)
        (Away.mk (ProjectiveGrading R n) (MvPolynomial.isHomogeneous_X R j) d F
          (homogeneous_mem_degree_smul hF))) at hg
  rw [hg, RingEquiv.apply_symm_apply]

set_option backward.isDefEq.respectTransparency false in
/-- A genuine original coordinate ratio is a unit in the true projective stalk exactly on the original coordinate open. -/
theorem nativeFormSection_X_unit_iff (ℓ j : Fin (n + 1)) (p : NativeProjectiveScheme R n)
    (hℓ : p ∈ nativeCoordinateOpen ℓ) :
    IsUnit ((NativeProjectiveScheme R n).presheaf.germ (nativeCoordinateOpen ℓ) p hℓ
      (nativeFormSection ℓ (X j))) ↔ p ∈ nativeCoordinateOpen j := by
  rw [← MulEquiv.isUnit_map (AlgebraicGeometry.Proj.stalkIso' (ProjectiveGrading R n) p),
    nativeFormSection_germ ℓ p hℓ (MvPolynomial.isHomogeneous_X R j),
    ← HomogeneousLocalization.isUnit_iff_isUnit_val]
  change IsUnit (Localization.mk (X j : MvPolynomial (Fin (n + 1)) R)
      (⟨(X ℓ) ^ 1, _⟩ : p.asHomogeneousIdeal.toIdeal.primeCompl)) ↔
    X j ∉ p.asHomogeneousIdeal
  rw [Localization.mk_eq_mk', IsLocalization.AtPrime.isUnit_mk'_iff]
  rfl

/-- The actual basic open of the entire coordinate ratio section is the genuine coordinate intersection. -/
theorem nativeFormSection_X_basicOpen (ℓ j : Fin (n + 1)) :
    (NativeProjectiveScheme R n).basicOpen (nativeFormSection ℓ (X j)) =
      nativeCoordinateOpen ℓ ⊓ nativeCoordinateOpen j := by
  ext p
  constructor
  · intro hp
    have hℓ := (NativeProjectiveScheme R n).basicOpen_le (nativeFormSection ℓ (X j)) hp
    exact ⟨hℓ, (nativeFormSection_X_unit_iff ℓ j p hℓ).mp
      (((NativeProjectiveScheme R n).mem_basicOpen _ p hℓ).mp hp)⟩
  · rintro ⟨hℓ, hj⟩
    exact ((NativeProjectiveScheme R n).mem_basicOpen _ p hℓ).mpr
      ((nativeFormSection_X_unit_iff ℓ j p hℓ).mpr hj)

set_option backward.isDefEq.respectTransparency false in
/-- Every original homogeneous form satisfies the full ratio identity in the actual overlap stalk, preserving nilpotents. -/
theorem nativeFormSection_germ_ratio (j ℓ : Fin (n + 1)) (p : NativeProjectiveScheme R n)
    (hj : p ∈ nativeCoordinateOpen j) (hℓ : p ∈ nativeCoordinateOpen ℓ)
    {F : MvPolynomial (Fin (n + 1)) R} {d : ℕ} (hF : F.IsHomogeneous d) :
    (NativeProjectiveScheme R n).presheaf.germ (nativeCoordinateOpen ℓ) p hℓ (nativeFormSection ℓ F) =
      (NativeProjectiveScheme R n).presheaf.germ (nativeCoordinateOpen j) p hj (nativeFormSection j F) *
        ((NativeProjectiveScheme R n).presheaf.germ (nativeCoordinateOpen ℓ) p hℓ
          (nativeFormSection ℓ (X j))) ^ d := by
  apply (AlgebraicGeometry.Proj.stalkIso' (ProjectiveGrading R n) p).injective
  simp only [map_mul, map_pow, nativeFormSection_germ ℓ p hℓ hF,
    nativeFormSection_germ j p hj hF,
    nativeFormSection_germ ℓ p hℓ (MvPolynomial.isHomogeneous_X R j)]
  apply HomogeneousLocalization.val_injective
  rw [HomogeneousLocalization.val_mul, HomogeneousLocalization.val_pow]
  let P := p.asHomogeneousIdeal.toIdeal
  let L := Localization.AtPrime P
  have hj' : (X j : MvPolynomial (Fin (n + 1)) R) ∈ P.primeCompl := hj
  have hℓ' : (X ℓ : MvPolynomial (Fin (n + 1)) R) ∈ P.primeCompl := hℓ
  let sj : P.primeCompl := ⟨X j ^ d, P.primeCompl.pow_mem hj' d⟩
  let sℓ : P.primeCompl := ⟨X ℓ ^ d, P.primeCompl.pow_mem hℓ' d⟩
  let sℓ1 : P.primeCompl := ⟨X ℓ ^ 1, P.primeCompl.pow_mem hℓ' 1⟩
  change Localization.mk F sℓ = Localization.mk F sj * (Localization.mk (X j) sℓ1) ^ d
  simp only [Localization.mk_eq_mk']
  rw [IsLocalization.mk'_eq_iff_eq_mul]
  change algebraMap (MvPolynomial (Fin (n + 1)) R) L F =
    (IsLocalization.mk' L F sj * (IsLocalization.mk' L (X j) sℓ1) ^ d) *
      algebraMap (MvPolynomial (Fin (n + 1)) R) L (X ℓ ^ d)
  have hratio : IsLocalization.mk' L (X j) sℓ1 *
      algebraMap (MvPolynomial (Fin (n + 1)) R) L (X ℓ) =
      algebraMap (MvPolynomial (Fin (n + 1)) R) L (X j) := by
    have h := IsLocalization.mk'_spec L (X j) sℓ1
    change IsLocalization.mk' L (X j) sℓ1 *
      algebraMap (MvPolynomial (Fin (n + 1)) R) L (X ℓ ^ 1) = _ at h
    exact (congrArg (fun b => IsLocalization.mk' L (X j) sℓ1 *
      algebraMap (MvPolynomial (Fin (n + 1)) R) L b) (pow_one (X ℓ))).symm.trans h
  rw [map_pow, mul_assoc, ← mul_pow, hratio, ← map_pow, IsLocalization.mk'_spec]

set_option backward.isDefEq.respectTransparency false in
/-- Actual overlap localization takes the entire original homogeneous-form section into the original ideal sheaf. -/
theorem nativeFormSection_restrict_mem (I : (NativeProjectiveScheme R n).IdealSheafData)
    (j ℓ : Fin (n + 1)) {F : MvPolynomial (Fin (n + 1)) R} {d : ℕ}
    (hF : F.IsHomogeneous d) (hI : coordinateDehom j F ∈ nativeCoordinateIdeal I j) :
    (NativeProjectiveScheme R n).presheaf.map
      (homOfLE ((NativeProjectiveScheme R n).basicOpen_le (nativeFormSection ℓ (X j)))).op
        (nativeFormSection ℓ F) ∈
      I.ideal ((NativeProjectiveScheme R n).affineBasicOpen
        (U := ⟨nativeCoordinateOpen ℓ, nativeCoordinateOpen_isAffine ℓ⟩)
        (nativeFormSection ℓ (X j))) := by
  let U : (NativeProjectiveScheme R n).affineOpens :=
    ⟨nativeCoordinateOpen ℓ, nativeCoordinateOpen_isAffine ℓ⟩
  let ξ := nativeFormSection (R := R) ℓ (X j)
  let W := (NativeProjectiveScheme R n).affineBasicOpen (U := U) ξ
  apply W.2.mem_ideal_iff.mpr
  intro p hp
  have hℓ : p ∈ nativeCoordinateOpen ℓ := (NativeProjectiveScheme R n).basicOpen_le ξ hp
  have hj : p ∈ nativeCoordinateOpen j := by
    have hw : p ∈ nativeCoordinateOpen ℓ ⊓ nativeCoordinateOpen j := by
      rwa [← nativeFormSection_X_basicOpen ℓ j]
    exact hw.2
  rw [← I.stalkIdeal_eq_affine p W hp]
  change (NativeProjectiveScheme R n).presheaf.germ
    ((NativeProjectiveScheme R n).basicOpen ξ) p hp
    ((NativeProjectiveScheme R n).presheaf.map
      (homOfLE ((NativeProjectiveScheme R n).basicOpen_le ξ)).op
      (nativeFormSection ℓ F)) ∈ I.stalkIdeal p
  rw [TopCat.Presheaf.germ_res_apply]
  rw [nativeFormSection_germ_ratio j ℓ p hj hℓ hF]
  exact Ideal.mul_mem_right _ _ (I.germ_mem_stalkIdeal p
    ⟨nativeCoordinateOpen j, nativeCoordinateOpen_isAffine j⟩ hj hI)

set_option backward.isDefEq.respectTransparency false in
/-- Actual ideal-sheaf localization clears the original homogeneous form by a real coordinate power on every other entire affine chart. -/
theorem exists_nativeFormSection_power_mem (I : (NativeProjectiveScheme R n).IdealSheafData)
    (j ℓ : Fin (n + 1)) {F : MvPolynomial (Fin (n + 1)) R} {d : ℕ}
    (hF : F.IsHomogeneous d) (hI : coordinateDehom j F ∈ nativeCoordinateIdeal I j) :
    ∃ N : ℕ, nativeFormSection ℓ (X j ^ N * F) ∈
      I.ideal ⟨nativeCoordinateOpen ℓ, nativeCoordinateOpen_isAffine ℓ⟩ := by
  let U : (NativeProjectiveScheme R n).affineOpens :=
    ⟨nativeCoordinateOpen ℓ, nativeCoordinateOpen_isAffine ℓ⟩
  let ξ := nativeFormSection (R := R) ℓ (X j)
  let W := (NativeProjectiveScheme R n).affineBasicOpen (U := U) ξ
  let : Algebra Γ(NativeProjectiveScheme R n, U) Γ(NativeProjectiveScheme R n, W) :=
    Scheme.algebra_section_section_basicOpen ξ
  have : IsLocalization.Away ξ Γ(NativeProjectiveScheme R n, W) :=
    U.2.isLocalization_basicOpen ξ
  have hx : algebraMap Γ(NativeProjectiveScheme R n, U) Γ(NativeProjectiveScheme R n, W)
      (nativeFormSection ℓ F) ∈ (I.ideal U).map
        (algebraMap Γ(NativeProjectiveScheme R n, U) Γ(NativeProjectiveScheme R n, W)) := by
    change (NativeProjectiveScheme R n).presheaf.map
      (homOfLE ((NativeProjectiveScheme R n).basicOpen_le ξ)).op (nativeFormSection ℓ F) ∈
      (I.ideal U).map ((NativeProjectiveScheme R n).presheaf.map
        (homOfLE ((NativeProjectiveScheme R n).basicOpen_le ξ)).op).hom
    rw [I.map_ideal_basicOpen U ξ]
    exact nativeFormSection_restrict_mem I j ℓ hF hI
  obtain ⟨m, ⟨N, rfl⟩, hN⟩ :=
    (IsLocalization.algebraMap_mem_map_algebraMap_iff (Submonoid.powers ξ)
      Γ(NativeProjectiveScheme R n, W) (I.ideal U) (nativeFormSection ℓ F)).mp hx
  refine ⟨N, ?_⟩
  simpa only [ξ, U, nativeFormSection, map_mul, map_pow] using hN

/-- A genuine common coordinate power makes an original chart numerator belong to the constructed homogeneous ideal on the entire chart cover. -/
theorem exists_nativeHomogeneousRepresentative_power_mem
    (I : (NativeProjectiveScheme R n).IdealSheafData) (j : Fin (n + 1))
    {F : MvPolynomial (Fin (n + 1)) R} {d : ℕ} (hF : F.IsHomogeneous d)
    (hI : coordinateDehom j F ∈ nativeCoordinateIdeal I j) :
    ∃ N : ℕ, X j ^ N * F ∈ nativeHomogeneousRepresentative I := by
  choose e he using fun ℓ : Fin (n + 1) => exists_nativeFormSection_power_mem I j ℓ hF hI
  let N := Finset.univ.sup e
  refine ⟨N, (mem_nativeHomogeneousRepresentative_of_isHomogeneous I
    ((MvPolynomial.isHomogeneous_X_pow j N).mul hF)).mpr ?_⟩
  intro ℓ
  have heN : e ℓ ≤ N := Finset.le_sup (f := e) (Finset.mem_univ ℓ)
  have hm := Ideal.mul_mem_left
    (I.ideal ⟨nativeCoordinateOpen ℓ, nativeCoordinateOpen_isAffine ℓ⟩)
    (nativeFormSection ℓ (X j ^ (N - e ℓ))) (he ℓ)
  change nativeFormSection ℓ (X j ^ N * F) ∈
    I.ideal ⟨nativeCoordinateOpen ℓ, nativeCoordinateOpen_isAffine ℓ⟩
  have hp : X j ^ (N - e ℓ) * (X j ^ e ℓ * F) = X j ^ N * F := by
    rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel heN]
  simpa only [nativeFormSection, map_mul, map_pow, ← hp] using hm

/-- The constructed original homogeneous ideal recovers the actual entire original ideal on every coordinate chart. -/
theorem nativeHomogeneousRepresentative_dehom_eq
    (I : (NativeProjectiveScheme R n).IdealSheafData) (j : Fin (n + 1)) :
    (nativeHomogeneousRepresentative I).toIdeal.map (coordinateDehom j).toRingHom =
      nativeCoordinateIdeal I j := by
  refine le_antisymm (nativeHomogeneousRepresentative_dehom_le I j) ?_
  intro a ha
  obtain ⟨d, F, hF, he⟩ := exists_homogeneous_coordinateDehom j a
  obtain ⟨N, hN⟩ := exists_nativeHomogeneousRepresentative_power_mem I j hF (he ▸ ha)
  have h := Ideal.mem_map_of_mem (coordinateDehom j).toRingHom hN
  have hX : coordinateDehom (R := R) j (X j) = 1 := by
    simp only [coordinateDehom, MvPolynomial.aeval_X, coordinateDehomCoord_self]
  simpa only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_mul, map_pow,
    hX, one_pow, one_mul, he] using h

set_option backward.isDefEq.respectTransparency false in
/-- Every actual projective ideal sheaf is the genuine quotient kernel of the constructed original homogeneous ideal, with equality as whole IdealSheafData. -/
theorem nativeHomogeneousRepresentative_quotientIdealSheaf
    (I : (NativeProjectiveScheme R n).IdealSheafData) :
    GradedQuotient.quotientIdealSheaf (ProjectiveGrading R n)
      (nativeHomogeneousRepresentative I) = I := by
  apply Scheme.IdealSheafData.ext_of_iSup_eq_top
    (fun j : Fin (n + 1) =>
      ⟨nativeCoordinateOpen j, nativeCoordinateOpen_isAffine j⟩)
    iSup_nativeCoordinateOpen_eq_top
  intro j
  apply Ideal.comap_injective_of_surjective
    (nativeCoordinateSectionsIso (R := R) j).hom.hom
    (nativeCoordinateSectionsIso (R := R) j).commRingCatIsoToRingEquiv.surjective
  rw [homogeneousQuotient_coordinateSectionIdeal,
    nativeHomogeneousRepresentative_dehom_eq]
  rfl

/-- Every actual polynomial-projective ideal sheaf has a genuine original homogeneous ideal whose quotient kernel is exactly that sheaf. -/
theorem exists_homogeneous_ideal_quotientIdealSheaf
    (I : (NativeProjectiveScheme R n).IdealSheafData) :
    ∃ J : HomogeneousIdeal (ProjectiveGrading R n),
      GradedQuotient.quotientIdealSheaf (ProjectiveGrading R n) J = I :=
  ⟨nativeHomogeneousRepresentative I, nativeHomogeneousRepresentative_quotientIdealSheaf I⟩

end DeJongAlterations.Geometry.ProjectiveIdeal
